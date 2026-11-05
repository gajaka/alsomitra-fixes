"""Integration checks: actual torch tensors -> actual Lean -> independent oracle."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import math
import random
import struct

import torch

from check_runtime import LOW, HIGH, pre
from torch_bridge import (Spec, Normalizer, assert_binding, bound_word, demo_model,
                          from_words, guarded_sample, infer_checked, model_identity,
                          observe, request_base, snapshot, upstream_normalizer, words)


def rational(word):
    value = struct.unpack("!f", struct.pack("!I", word))[0]
    return Q(value) if math.isfinite(value) else None


def run_checks(client):
    checks, rejections = 0, 0
    def require(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise AssertionError(message)

    def rejects(fn, contains=""):
        nonlocal rejections
        try:
            fn()
        except (ValueError, RuntimeError) as error:
            require(contains in str(error), f"unexpected rejection: {error}")
            rejections += 1
        else:
            raise AssertionError("expected rejection")

    rng = random.Random(20261105)
    patterns = [(sign << 31) | (exponent << 23) | fraction
                for sign in (0, 1) for exponent in range(256)
                for fraction in (0, 1, 0x3fffff, 0x7fffff)]
    patterns += [rng.randrange(2**32) for _ in range(2048)]
    for start in range(0, len(patterns), 128):
        batch = patterns[start:start+128]
        decoded = client.request(dict(action="decode", words=batch))["values"]
        require(len(decoded) == len(batch), "decoder response length")
        for word, value in zip(batch, decoded):
            expected = rational(word)
            require(value is None if expected is None else Q(value) == expected, f"decode {word:#x}")
    invalid = client.request(dict(action="decode", words=[2**32, 2**64]))
    require(invalid["values"] == [None, None], "oversized word rejected")
    for malformed in (-1, 1.5, "0", True):
        result = client.request(dict(action="decode", words=[malformed]), allow_error=True)
        require(result.get("status") == "error", "non-natural word rejected")

    finite = [w for w in patterns if rational(w) is not None]
    require(words(from_words(finite)) == finite, "bitcast preserves finite words and signed zeros")

    # Rounding direction and adjacent representable values, including subnormals.
    boundaries = [Q(0), Q(1, 10), Q(-3, 10), Q(1, 2**150), Q(-1, 2**150)]
    boundaries += [Q(rng.randrange(-10000, 10000), 97) for _ in range(50)]
    for bound in boundaries:
        lo, hi = bound_word(bound, upwards=True), bound_word(bound, upwards=False)
        require(rational(hi) <= bound <= rational(lo), "inward directed rounding")
        previous = torch.nextafter(from_words([lo]), torch.tensor([-float("inf")], dtype=torch.float32))
        following = torch.nextafter(from_words([hi]), torch.tensor([float("inf")], dtype=torch.float32))
        require(Q(previous.item()) < bound, "ceil is the least representable value")
        require(Q(following.item()) > bound, "floor is the greatest representable value")
    rejects(lambda: bound_word(Q(2)**200, upwards=True), "no finite")
    rejects(lambda: bound_word(-Q(2)**200, upwards=False), "no finite")

    spec, normalizer = Spec(), upstream_normalizer()
    base = request_base(spec, normalizer)
    unit = torch.tensor(list(product((0., 1.), repeat=6)), dtype=torch.float32)
    generator = torch.Generator().manual_seed(20261105)
    unit = torch.cat((unit, torch.rand((64, 6), dtype=torch.float32, generator=generator)))
    candidate = guarded_sample(client, spec, normalizer, unit)
    offset, scale = list(map(rational, normalizer.offset)), list(map(rational, normalizer.scale))
    for row in candidate:
        point = [rational(w)*s+o for w, s, o in zip(words(row), scale, offset)]
        require(pre(spec.fields(), point), "guarded candidate direct physical predicate")

    above = torch.nextafter(torch.tensor(.5, dtype=torch.float32), torch.tensor(float("inf"), dtype=torch.float32))
    outputs = torch.tensor([0., .5, above.item()] * 43, dtype=torch.float32)[:len(candidate)].reshape(-1, 1)
    observations = observe(client, spec, normalizer, candidate, outputs)
    materialized = normalizer.materialize(candidate)
    materialized_out = torch.tensor(.181, dtype=torch.float32) + torch.tensor(.012, dtype=torch.float32)*outputs
    for index, (row, output, result) in enumerate(zip(candidate, outputs, observations)):
        z = list(map(rational, words(row)))
        physical = [a*b+c for a,b,c in zip(z, scale, offset)]
        y = rational(words(output)[0])
        require(list(map(Q, result["normalized"])) == z, "exact input decoding")
        require(list(map(Q, result["physical"])) == physical, "exact affine reconstruction")
        require(result["verdict"] == ("satisfied" if y <= Q(1,2) else "violated"), "normalized output contract")
        require(Q(result["physical_output"]) == Q(181,1000)+Q(12,1000)*y, "exact output units")
        require(Q(result["loss"]) == max(0,Q(181,1000)+Q(12,1000)*y-Q(187,1000)), "exact loss")
        p = [Q(float(x)) for x in materialized[index]]
        out = Q(materialized_out[index].item())
        expected = "outside" if not pre(spec.fields(), p) else "satisfied" if out <= Q(187,1000) else "violated"
        require(list(map(Q, result["rounded_physical"])) == p, "actual materialized input")
        require(Q(result["rounded_physical_output"]) == out, "actual materialized output")
        require(result["rounded_verdict"] == expected, "separate physical observation")

    # Reproduce what goes wrong with ordinary float32 affine corner generation.
    physical_low, physical_high = list(map(float, LOW)), list(map(float, HIGH))
    physical_low[5] = -10.
    physical_high[1], physical_high[2], physical_high[5] = -.3, -.12, -8.
    lo, hi = torch.tensor(physical_low), torch.tensor(physical_high)
    original_like = (lo + unit[:64]*(hi-lo) - from_words(normalizer.offset)) / from_words(normalizer.scale)
    naive_rejected = sum(not client.request(dict(base, action="gate", input_bits=words(row)))["admissible"]
                         for row in original_like)
    require(naive_rejected > 0, "ordinary float32 boundary generation can leave exact region")

    middle = guarded_sample(client, spec, normalizer, torch.full((1,6), .5, dtype=torch.float32))
    witness = observe(client, spec, normalizer, middle, above.reshape(1,1))[0]
    rounded_output = torch.tensor(.181, dtype=torch.float32) + torch.tensor(.012, dtype=torch.float32)*above
    require(witness["verdict"] == "violated" and witness["rounded_verdict"] == "satisfied", "real rounding disagreement")
    require(bool(rounded_output <= torch.tensor(.187, dtype=torch.float32)), "naive float32 comparison accepts")

    # Accepted input -> next representable point outside each tight face -> outside.
    bounds = client.request(dict(base, action="bounds"))
    outside_count = 0
    for axis, side, direction in ((1,"normalized_hi",float("inf")), (2,"normalized_hi",float("inf")),
                                  (5,"normalized_lo",-float("inf")), (5,"normalized_hi",float("inf"))):
        word = bound_word(Q(bounds[side][axis]), upwards=(side == "normalized_lo"))
        point = middle.clone()
        point[0,axis] = torch.nextafter(from_words([word]), torch.tensor([direction], dtype=torch.float32))[0]
        reply = observe(client, spec, normalizer, point, torch.tensor([[.5]], dtype=torch.float32))[0]
        require(reply["verdict"] == "outside", "one float32 step past a tight face")
        outside_count += 1

    identity = Normalizer.capture(torch.zeros(6), torch.ones(6))
    collapsed = Spec(anchor="0", band_upper="0")
    degenerate = guarded_sample(client, collapsed, identity, torch.full((1,6), .5))
    require(degenerate[0,5].item() == 0, "representable zero-width region")
    rejects(lambda: guarded_sample(client, collapsed, normalizer, torch.full((1,6), .5)), "no float32 representative")
    rejects(lambda: guarded_sample(client, Spec(band_upper="-3/10", velocity_upper="2"), normalizer, unit), "empty exact")
    custom = Normalizer.capture(torch.tensor([1.,-8.,9.,1.,-2.,3.]), torch.tensor([.25,5.5,.001,8.,2.,.5]))
    custom_points = guarded_sample(client, spec, custom, unit[:64])
    co, cs = list(map(rational, custom.offset)), list(map(rational, custom.scale))
    for row in custom_points:
        require(pre(spec.fields(), [rational(w)*s+o for w,s,o in zip(words(row),cs,co)]), "custom captured normalizer")

    # Parser/gate rejection cannot turn NaN, invalid scales, etc. into success.
    good = dict(base, action="observe", input_bits=words(middle[0]), output_bits=words(above)[0])
    for word in (0x7f800000, 0xff800000, 0x7fc00001, 0xffc00001, 2**32):
        bad = [word]+good["input_bits"][1:]
        require(client.request(dict(base, action="gate", input_bits=bad))["admissible"] is False, "invalid input gate")
        reply = client.request(dict(good, output_bits=word), allow_error=True)
        require(reply.get("status") == "error", "invalid output rejection")
    bad_requests = [dict(good, input_bits=[0]*5), dict(good, output_bits=-1),
                    dict(good, typo="ignored?"), dict(good, physical_bits=[0]*6),
                    dict(good, physical_output_bits=0), dict(good, anchor="0.1"),
                    dict(good, scale_bits=[0]*6), dict(good, scale_bits=[0x80000000]*6),
                    dict(good, offset_bits=[0x7f800000]*6)]
    for request in bad_requests:
        require(client.request(request, allow_error=True).get("status") == "error", "malformed/config rejection")
    rejects(lambda: snapshot(torch.ones(6,dtype=torch.float64)), "torch.float32")
    rejects(lambda: snapshot(torch.tensor([float("nan")])), "non-finite")
    rejects(lambda: observe(client,spec,normalizer,middle,torch.tensor([.5])), "shape")
    rejects(lambda: guarded_sample(client,spec,normalizer,torch.full((1,6),1.01)), "unit coordinates")
    rejects(lambda: guarded_sample(client,spec,normalizer,torch.zeros((0,6))), "nonempty")

    model = demo_model()
    before = model_identity(model)
    inference_inputs = candidate[:8].clone()
    inferred, receipt = infer_checked(client, spec, normalizer, model, inference_inputs)
    require(before == model_identity(model), "caller model unchanged")
    assert_binding(receipt, spec, normalizer, model, inference_inputs, inferred)
    require(len(receipt["payload"]["observations"]) == 8, "one inference verdict per row")
    for y,result in zip(inferred, receipt["payload"]["observations"]):
        require(result["verdict"] == ("satisfied" if Q(y.item())<=Q(1,2) else "violated"), "actual inference output checked")
    changed_input = inference_inputs.clone()
    changed_input[0,0] = torch.nextafter(changed_input[0,0],torch.tensor(float("inf")))
    rejects(lambda: assert_binding(receipt,spec,normalizer,model,changed_input,inferred), "does not bind")
    changed_output = inferred.clone()
    changed_output[0,0] = torch.nextafter(changed_output[0,0],torch.tensor(float("inf")))
    rejects(lambda: assert_binding(receipt,spec,normalizer,model,inference_inputs,changed_output), "does not bind")
    changed_model = deepcopy(model)
    with torch.no_grad():
        changed_model[0].weight[0,0] += .25
    rejects(lambda: assert_binding(receipt,spec,normalizer,changed_model,inference_inputs,inferred), "does not bind")
    rejects(lambda: assert_binding(receipt,Spec(anchor="11"),normalizer,model,inference_inputs,inferred), "does not bind")
    rejects(lambda: assert_binding(receipt,spec,identity,model,inference_inputs,inferred), "does not bind")
    changed_receipt = deepcopy(receipt)
    changed_receipt["payload"]["observations"][0]["verdict"] = "tampered"
    rejects(lambda: assert_binding(changed_receipt,spec,normalizer,model,inference_inputs,inferred), "contents changed")
    rejects(lambda: model_identity(torch.nn.Sequential(torch.nn.Dropout()).eval()), "only Sequential")

    return dict(assertions=checks, binary32_words_compared=len(patterns), guarded_samples=len(candidate)+len(custom_points)+2,
                naive_corner_rejections=naive_rejected, adjacent_outside_cases=outside_count,
                expected_python_rejections=rejections, inference_rows=8, example_receipt=receipt,
                boundary_witness=dict(normalized_output=above.item(), normalized_bits=words(above)[0],
                                      torch_materialized_output=rounded_output.item(),
                                      torch_comparison=True, exact_verdict=witness["verdict"],
                                      materialized_verdict=witness["rounded_verdict"]))
