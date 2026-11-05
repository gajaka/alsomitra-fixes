"""CPU float32 observations checked by the executable Lean Property2 core.

No network-wide guarantee: receipts bind a particular input/output observation.
Run verify_float32.py before using LeanClient with its default freshness check.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import select
import struct
import subprocess
import tempfile

import torch

ROOT = Path(__file__).resolve().parent
SOURCE_NAMES = ("Property2.lean", "Protocol.lean", "Float32.lean", "Float32Main.lean",
                "Float32Audit.lean", "torch_bridge.py", "check_float32.py", "verify_float32.py",
                "check_upstream_float32.py")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_hashes():
    return {name: sha(ROOT / name) for name in SOURCE_NAMES}


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                    allow_nan=False).encode()).hexdigest()


def snapshot(tensor, shape=None):
    if not isinstance(tensor, torch.Tensor) or tensor.device.type != "cpu" or tensor.dtype != torch.float32:
        raise ValueError("a CPU torch.float32 tensor is required; no implicit cast")
    if tensor.layout != torch.strided or (shape is not None and tuple(tensor.shape) != tuple(shape)):
        raise ValueError("unexpected tensor layout or shape")
    value = tensor.detach().clone().contiguous()
    if not bool(torch.isfinite(value).all()):
        raise ValueError("non-finite observation")
    return value


def words(tensor):
    value = snapshot(tensor)
    return [int(x) & 0xffffffff for x in value.reshape(-1).view(torch.int32).tolist()]


def from_words(values):
    if any(type(x) is not int or not 0 <= x < 2**32 for x in values):
        raise ValueError("unsigned 32-bit words required")
    signed = [x if x < 2**31 else x - 2**32 for x in values]
    return torch.tensor(signed, dtype=torch.int32).view(torch.float32)


def exact_word(word):
    """Independent host decode. A finite binary32 value is exact in binary64."""
    value = struct.unpack("!f", struct.pack("!I", word))[0]
    return Q(value)  # rejects infinity and NaN


@dataclass(frozen=True)
class Spec:
    anchor: str = "10"
    band_upper: str = "2"
    velocity_upper: str = "-3/10"
    angular_upper: str = "-3/25"

    def fields(self):
        return {k: str(Q(v)) for k, v in vars(self).items()}


@dataclass(frozen=True)
class Normalizer:
    offset: tuple[int, ...]
    scale: tuple[int, ...]

    @classmethod
    def capture(cls, offset, scale):
        offset, scale = snapshot(offset, (6,)), snapshot(scale, (6,))
        if not bool((scale > 0).all()):
            raise ValueError("positive scales required")
        return cls(tuple(words(offset)), tuple(words(scale)))

    def fields(self):
        # Also validate direct construction, not just capture().
        self.capture(from_words(self.offset), from_words(self.scale))
        return dict(offset_bits=list(self.offset), scale_bits=list(self.scale))

    def materialize(self, z):
        # Separate eager operations, captured as their own observation.
        return z * from_words(self.scale) + from_words(self.offset)


def upstream_normalizer():
    lo = torch.tensor([.967568, -.607397, -.356973, -.968479, .482421, -41.681405], dtype=torch.float32)
    hi = torch.tensor([3.489893, -.043021, .049180, -.068003, 41.714717, 4.197234], dtype=torch.float32)
    return Normalizer.capture(lo, hi - lo)


class LeanClient:
    """One sequential JSON-lines session; source/build freshness is checked.

    verify_float32.py uses verified=False while constructing the new report.
    This escape hatch is only for the verification driver, not a proof claim.
    """
    def __init__(self, *, verified=True, transcript=None):
        if verified:
            report = json.loads((ROOT / "results/float32_verification.json").read_text())
            if report.get("status") != "PASS" or report["sources_sha256"] != source_hashes():
                raise RuntimeError("run verify_float32.py for these exact sources first")
            if any(sha(ROOT / name) != value for name, value in report["artifacts_sha256"].items()):
                raise RuntimeError("compiled artifacts changed; run verify_float32.py")
        env = os.environ.copy()
        env["LEAN_PATH"] = str(ROOT / ".build") + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        self.stderr = tempfile.TemporaryFile(mode="w+t")
        self.process = subprocess.Popen(["lake", "env", "lean", "--run", str(ROOT / "Float32Main.lean")],
                                        cwd=ROOT.parent / "lean", env=env, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=self.stderr, text=True, bufsize=1)
        self.transcript = Path(transcript).open("w") if transcript else None
        self.requests = 0

    def request(self, value, *, allow_error=False):
        self.process.stdin.write(json.dumps(value, allow_nan=False) + "\n")
        self.process.stdin.flush()
        if not select.select([self.process.stdout], [], [], 60)[0]:
            raise TimeoutError("Lean response exceeded 60 seconds")
        line = self.process.stdout.readline()
        if not line:
            self.stderr.seek(0)
            raise RuntimeError("Lean stopped: " + self.stderr.read())
        result = json.loads(line)
        self.requests += 1
        if self.transcript:
            self.transcript.write(json.dumps(dict(request=value, reply=result), sort_keys=True) + "\n")
            self.transcript.flush()
        if result.get("status") == "error" and not allow_error:
            raise ValueError(result["message"])
        return result

    def __enter__(self):
        return self

    def __exit__(self, kind, error, trace):
        try:
            self.process.stdin.close()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)
            self.stderr.seek(0)
            diagnostics = self.stderr.read()
            if kind is None and (self.process.returncode or diagnostics):
                raise RuntimeError("Lean exit/diagnostics: " + diagnostics)
        finally:
            self.process.stdout.close()
            self.stderr.close()
            if self.transcript:
                self.transcript.close()


def request_base(spec, normalizer):
    return {**spec.fields(), **normalizer.fields()}


def bound_word(bound, *, upwards):
    """Ceil/floor in the ordered set of finite binary32 values (exact search)."""
    def bits(key):
        return key ^ 0x80000000 if key >= 0x80000000 else ~key & 0xffffffff
    left, right = 0x00800000, 0xff7fffff
    if upwards and bound > exact_word(bits(right)) or not upwards and bound < exact_word(bits(left)):
        raise ValueError("no finite float32 representative")
    while left < right:
        middle = (left + right + (not upwards)) // 2
        value = exact_word(bits(middle))
        if upwards:
            if value < bound:
                left = middle + 1
            else:
                right = middle
        elif value > bound:
            right = middle - 1
        else:
            left = middle
    return bits(left)


def guarded_sample(client, spec, normalizer, unit):
    unit = snapshot(unit)
    if unit.ndim != 2 or unit.shape[1] != 6 or unit.shape[0] == 0:
        raise ValueError("nonempty [N,6] unit tensor required")
    if not bool(((0 <= unit) & (unit <= 1)).all()):
        raise ValueError("unit coordinates must lie in [0,1]")
    base = request_base(spec, normalizer)
    bounds = client.request(dict(base, action="bounds"))
    if not bounds["nonempty"]:
        raise ValueError("empty exact region")
    lo = [bound_word(Q(x), upwards=True) for x in bounds["normalized_lo"]]
    hi = [bound_word(Q(x), upwards=False) for x in bounds["normalized_hi"]]
    if any(exact_word(a) > exact_word(b) for a, b in zip(lo, hi)):
        raise ValueError("exact region has no float32 representative")
    low, high = from_words(lo), from_words(hi)
    raw = snapshot(low + unit * (high - low))  # overflow is rejected, not certified
    candidate = torch.minimum(high, torch.maximum(low, raw))
    for row in candidate:
        result = client.request(dict(base, action="gate", input_bits=words(row)))
        if not result["admissible"]:
            raise RuntimeError("generated candidate rejected by exact Lean gate")
    return candidate


def observe(client, spec, normalizer, inputs, outputs):
    inputs = snapshot(inputs)
    if inputs.ndim != 2 or inputs.shape[1] != 6 or inputs.shape[0] == 0:
        raise ValueError("nonempty [N,6] input tensor required")
    outputs = snapshot(outputs, (inputs.shape[0], 1))
    physical = snapshot(normalizer.materialize(inputs))
    physical_output = snapshot(torch.tensor(.181, dtype=torch.float32)
                               + torch.tensor(.012, dtype=torch.float32) * outputs)
    base = request_base(spec, normalizer)
    return [client.request(dict(base, action="observe", input_bits=words(z), output_bits=words(y)[0],
                                physical_bits=words(p), physical_output_bits=words(o)[0]))
            for z, y, p, o in zip(inputs, outputs, physical, physical_output)]


def model_identity(model):
    """Deliberately small eager inference fragment; no arbitrary custom forward."""
    if type(model) is not torch.nn.Sequential or model.training:
        raise ValueError("an eval-mode Sequential model is required")
    description = []
    for name, module in model.named_modules(remove_duplicate=False):
        if type(module) not in (torch.nn.Sequential, torch.nn.Linear, torch.nn.ReLU, torch.nn.Identity):
            raise ValueError("only Sequential/Linear/ReLU/Identity are supported")
        if any(getattr(module, attr) for attr in ("_forward_hooks", "_forward_pre_hooks", "_backward_hooks")):
            raise ValueError("module hooks are outside this bridge's scope")
        if module.training:
            raise ValueError("all modules must be in eval mode")
        if "forward" in vars(module) or getattr(module, "_compiled_call_impl", None) is not None:
            raise ValueError("custom/compiled forward is outside this bridge's scope")
        description.append(dict(path=name, type=type(module).__name__, representation=module.extra_repr()))
    state = {name: dict(shape=list(value.shape), words=words(value)) for name, value in model.state_dict().items()}
    return canonical_hash(dict(graph=description, state=state))


def binding(spec, normalizer, model, inputs, outputs):
    return dict(spec=spec.fields(), normalizer=normalizer.fields(), model_sha256=model_identity(model),
                contract_sources={name:sha(ROOT/name) for name in ("Property2.lean","Float32.lean","torch_bridge.py")},
                input_shape=list(inputs.shape), input_bits=words(inputs),
                output_shape=list(outputs.shape), output_bits=words(outputs),
                torch_version=torch.__version__, device="cpu", dtype="float32")


def infer_checked(client, spec, normalizer, model, inputs):
    """Run a private snapshot and bind its actual outputs to pointwise verdicts."""
    before = model_identity(model)
    frozen = deepcopy(model)
    captured = snapshot(inputs)
    if captured.ndim != 2 or captured.shape[1] != 6 or captured.shape[0] == 0:
        raise ValueError("nonempty [N,6] input tensor required")
    input_bits = words(captured)
    with torch.inference_mode(), torch.autocast("cpu", enabled=False):
        output = snapshot(frozen(captured), (captured.shape[0], 1))
    if words(captured) != input_bits or model_identity(frozen) != before or model_identity(model) != before:
        raise RuntimeError("input/model changed during inference")
    observed = observe(client, spec, normalizer, captured, output)
    payload = dict(binding=binding(spec, normalizer, frozen, captured, output), observations=observed)
    receipt = dict(payload=payload, sha256=canonical_hash(payload))
    return output, receipt


def assert_binding(receipt, spec, normalizer, model, inputs, outputs):
    if canonical_hash(receipt["payload"]) != receipt["sha256"]:
        raise ValueError("receipt contents changed")
    if receipt["payload"]["binding"] != binding(spec, normalizer, model, inputs, outputs):
        raise ValueError("receipt does not bind these artifacts")


def demo_model():
    """Fixed non-trained witness, not an Alsomitra model or a model certificate."""
    model = torch.nn.Sequential(torch.nn.Linear(6, 2), torch.nn.ReLU(), torch.nn.Linear(2, 1))
    with torch.no_grad():
        model[0].weight.copy_(torch.tensor([[1., -.5, .25, 0., 0., .5], [-.25, .5, 0., 0., .25, 0.]]))
        model[0].bias.copy_(torch.tensor([.1, -.1]))
        model[2].weight.copy_(torch.tensor([[.5, -.25]]))
        model[2].bias.fill_(.1)
    return model.eval()


if __name__ == "__main__":
    with LeanClient() as client:
        spec, normalizer = Spec(), upstream_normalizer()
        inputs = guarded_sample(client, spec, normalizer, torch.full((1, 6), .5, dtype=torch.float32))
        outputs, receipt = infer_checked(client, spec, normalizer, demo_model(), inputs)
        print(json.dumps(receipt, indent=2))
