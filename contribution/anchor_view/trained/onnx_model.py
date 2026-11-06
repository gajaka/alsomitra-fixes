"""Strict importer for the two pinned SAIV dense/ReLU ONNX controllers.

This supports exactly their three Gemm/Relu pairs, including the output ReLU.
It is an executable adapter, not a formally verified ONNX compiler.
"""
import numpy as np
import onnx
from onnx import numpy_helper
import torch
from torch import nn


def require(condition, message):
    if not condition:
        raise AssertionError(message)


class DenseController(nn.Module):
    def __init__(self, graph):
        super().__init__()
        onnx.checker.check_model(graph)
        require(len(graph.graph.input) == len(graph.graph.output) == 1,
                'Expected one input and one output')
        require([n.op_type for n in graph.graph.node] == ['Gemm', 'Relu'] * 3,
                'Expected three Gemm/Relu pairs, including the output ReLU')
        require(not graph.functions, 'Local ONNX functions are unsupported')
        for value, shape in [(graph.graph.input[0], [1, 6]),
                             (graph.graph.output[0], [1, 1])]:
            require(value.type.tensor_type.elem_type == onnx.TensorProto.FLOAT,
                    'Expected float32 interface')
            require([d.dim_value for d in value.type.tensor_type.shape.dim] == shape,
                    'Unexpected ONNX interface shape')
        arrays = {}
        for t in graph.graph.initializer:
            require(not t.external_data and t.data_type == onnx.TensorProto.FLOAT,
                    'Expected embedded float32 weights')
            require(t.name not in arrays, 'Duplicate initializer')
            arrays[t.name] = numpy_helper.to_array(t).copy()
        self.layers = nn.ModuleList()
        self.arrays = []
        previous = graph.graph.input[0].name
        used = set()
        for i, (ins, outs) in enumerate([(6, 6), (6, 4), (4, 1)]):
            gemm, relu = graph.graph.node[2*i:2*i+2]
            attrs = {a.name: onnx.helper.get_attribute_value(a) for a in gemm.attribute}
            require(not gemm.domain and not relu.domain, 'Custom ONNX operator domain')
            require(set(attrs) <= {'alpha', 'beta', 'transA', 'transB'}, 'Unknown Gemm attribute')
            require(attrs.get('alpha', 1.) == attrs.get('beta', 1.) == 1.
                    and attrs.get('transA', 0) == attrs.get('transB', 0) == 0,
                    'Unsupported Gemm orientation or scaling')
            require(len(gemm.input) == 3 and len(gemm.output) == 1
                    and gemm.input[0] == previous, 'Unexpected graph wiring')
            require(list(relu.input) == list(gemm.output) and len(relu.output) == 1
                    and not relu.attribute, 'Unexpected ReLU wiring or attributes')
            w, b = [arrays[name] for name in gemm.input[1:]]
            require(w.shape == (ins, outs) and b.shape == (outs,), 'Wrong layer dimensions')
            require(np.isfinite(w).all() and np.isfinite(b).all(), 'Nonfinite weights')
            with torch.random.fork_rng(devices=[]):
                layer = nn.Linear(ins, outs)
            with torch.no_grad():
                layer.weight.copy_(torch.from_numpy(w.T.copy()))
                layer.bias.copy_(torch.from_numpy(b))
            require(np.array_equal(layer.weight.detach().numpy().T.view(np.uint32),
                                   w.view(np.uint32)), 'Weight bits changed during import')
            require(np.array_equal(layer.bias.detach().numpy().view(np.uint32),
                                   b.view(np.uint32)), 'Bias bits changed during import')
            self.layers.append(layer)
            self.arrays.append((w, b))
            used.update(gemm.input[1:])
            previous = relu.output[0]
        require(used == set(arrays), 'Unused or missing initializers')
        require(previous == graph.graph.output[0].name, 'Unexpected graph output')
        self.eval()

    def forward(self, x):
        for layer in self.layers:
            x = torch.relu(layer(x))
        return x

    def numpy_jacobian(self, x):
        """Independent real-arithmetic chain rule on imported float32 constants."""
        z = x.astype(np.float64)
        jac = np.broadcast_to(np.eye(6), (len(z), 6, 6)).copy()
        margin = np.full(len(z), np.inf)
        for w, b in self.arrays:
            pre = z @ w.astype(np.float64) + b.astype(np.float64)
            margin = np.minimum(margin, np.min(np.abs(pre), axis=1))
            jac = np.einsum('bki,ij->bkj', jac, w.astype(np.float64))
            jac *= (pre > 0)[:, None, :]
            z = np.maximum(pre, 0)
        return z, jac[:, :, 0], margin


class FrameworkInputs(nn.Module):
    """Bridge the framework's rounded normalization to the SAIV normalization.

Outputs stay normalized: the original postcondition already maps its physical
0.187 threshold to the model's normalized output scale (approximately 0.5).
"""
    def __init__(self, core, precondition, centres, scales):
        super().__init__()
        self.core = core
        self.register_buffer('framework_min', precondition.min.clone())
        self.register_buffer('framework_scale', (precondition.max-precondition.min).clone())
        self.register_buffer('saiv_centre', torch.tensor(centres, dtype=torch.float32))
        self.register_buffer('saiv_scale', torch.tensor(scales, dtype=torch.float32))
        self.eval()

    def to_saiv(self, x):
        return (x*self.framework_scale + self.framework_min - self.saiv_centre)/self.saiv_scale

    def from_saiv(self, x):
        return (x*self.saiv_scale + self.saiv_centre - self.framework_min)/self.framework_scale

    def forward(self, x):
        return self.core(self.to_saiv(x))
