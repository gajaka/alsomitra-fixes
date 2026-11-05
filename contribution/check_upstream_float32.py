"""Optional integration with the pinned, unmodified original Alsomitra sources.

Uses deterministic initialization, not training or a certified checkpoint.
"""
from fractions import Fraction as Q
import importlib
import importlib.util
from pathlib import Path
import subprocess
import sys

import torch

from torch_bridge import (Normalizer, Spec, canonical_hash, guarded_sample, observe,
                          sha, snapshot, upstream_normalizer, words)

PIN = "616df1e5baaabf7b42dc26320c00fb297903c87a"
FILES = ("examples/models.py", "src/property_driven_ml/constraints/preconditions.py",
         "src/property_driven_ml/constraints/postconditions.py")


def run_upstream(client, path):
    repo = Path(path).resolve()
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=repo)
    if git("rev-parse", "HEAD").decode().strip() != PIN:
        raise ValueError("unexpected upstream revision")
    for name in FILES:
        if (repo/name).read_bytes() != git("show", PIN+":"+name):
            raise ValueError("modified upstream source: " + name)
    source_hashes = {name: sha(repo/name) for name in FILES}
    module_spec = importlib.util.spec_from_file_location("contribution_upstream_models", repo/FILES[0])
    models = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(models)
    sys.path.insert(0, str(repo/"src"))
    try:
        pre_module = importlib.import_module("property_driven_ml.constraints.preconditions")
        post_module = importlib.import_module("property_driven_ml.constraints.postconditions")
    finally:
        sys.path.pop(0)
    if Path(pre_module.__file__).resolve() != repo/FILES[1] or Path(post_module.__file__).resolve() != repo/FILES[2]:
        raise ValueError("import resolved to a different upstream installation")

    checks = 0
    def require(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise AssertionError(message)

    device = torch.device("cpu")
    precondition = pre_module.AlsomitraProperty2(device, v_y_threshold=-.3, y_threshold=2., omega_threshold=-.12)
    postcondition = post_module.AlsomitraOutputPostcondition(device, hi=.187)
    normalizer = Normalizer.capture(precondition.min, precondition.max-precondition.min)
    require(normalizer == upstream_normalizer(), "actual upstream normalizer bit identity")
    spec = Spec()
    generator = torch.Generator().manual_seed(20261105)
    inputs = guarded_sample(client, spec, normalizer, torch.rand((16,6), generator=generator))
    with torch.random.fork_rng(devices=[]):
        torch.manual_seed(20261105)
        model = models.AlsomitraNet().cpu().float().eval()
    def state():
        return {name: dict(shape=list(value.shape), words=words(value)) for name,value in model.state_dict().items()}
    before, captured = state(), words(inputs)
    with torch.inference_mode(), torch.autocast("cpu", enabled=False):
        outputs = snapshot(model(inputs), (16,1))
        physical = snapshot(precondition.denormalize(inputs))
        physical_output = snapshot(postcondition.denormalize(outputs))
    require(state() == before and words(inputs) == captured, "upstream inference leaves captured artifacts unchanged")
    observations = observe(client,spec,normalizer,inputs,outputs)
    for index, (output, result) in enumerate(zip(outputs, observations)):
        require(result["verdict"] == ("satisfied" if Q(output.item()) <= Q(1,2) else "violated"), "original network output checked")
        require(list(map(Q,result["rounded_physical"])) == [Q(float(x)) for x in physical[index]], "original input denormalization")
        require(Q(result["rounded_physical_output"]) == Q(physical_output[index].item()), "original output denormalization")
    above = torch.nextafter(torch.tensor(.5), torch.tensor(float("inf")))
    point = guarded_sample(client,spec,normalizer,torch.full((1,6),.5))
    witness = observe(client,spec,normalizer,point,above.reshape(1,1))[0]
    original_materialized = postcondition.denormalize(above)
    require(Q(witness["rounded_physical_output"]) == Q(original_materialized.item()), "boundary uses original denormalizer")
    require(witness["verdict"] == "violated", "boundary violates rational contract")
    require(bool(above <= postcondition.hi), "original normalized threshold accepts boundary witness")
    payload = dict(upstream_revision=PIN, sources_sha256=source_hashes, initialization_seed=20261105,
                   model="original examples.models.AlsomitraNet (6-64-32-1, ReLU)", trained=False,
                   spec=spec.fields(), normalizer=normalizer.fields(), state_sha256=canonical_hash(before),
                   input_shape=list(inputs.shape), input_bits=captured, output_shape=list(outputs.shape),
                   output_bits=words(outputs), observations=observations,
                   torch_version=torch.__version__, device="cpu", dtype="float32")
    require(all(sha(repo/name) == value for name,value in source_hashes.items()), "upstream sources unchanged")
    return dict(assertions=checks, inference_rows=16, receipt=dict(payload=payload, sha256=canonical_hash(payload)),
                boundary=dict(normalized_output=above.item(), original_normalized_cap=postcondition.hi.item(),
                              original_accepts=True, exact_verdict=witness["verdict"],
                              original_materialized_output=original_materialized.item()))
