"""Independent Fraction oracle against the actual executable Lean implementation.

No PyTorch, training, random-network claims, or hand-transcribed Lean evaluator.
The oracle checks the physical predicate directly and compares exact values.
"""
from fractions import Fraction as Q
from itertools import product
import random


LOW = tuple(map(Q, ("0.967568", "-0.607397", "-0.356973", "-0.968479", "0.482421", "-41.681405")))
HIGH = tuple(map(Q, ("3.489893", "-0.043021", "0.049180", "-0.068003", "41.714717", "4.197234")))


def strings(values):
    return [str(x) for x in values]


def normalizer(request):
    if "normalization" in request:
        n = request["normalization"]
        return tuple(map(Q, n["offset"])), tuple(map(Q, n["scale"]))
    return LOW, tuple(b - a for a, b in zip(LOW, HIGH))


def pre(request, point):
    """Direct physical predicate; deliberately does not call a box compiler."""
    anchor = Q(request["anchor"])
    return (
        all(lo <= x <= hi for lo, x, hi in zip(LOW, point, HIGH))
        and 0 <= anchor + point[5] <= Q(request.get("band_upper", "2"))
        and point[1] <= Q(request.get("velocity_upper", "-3/10"))
        and point[2] <= Q(request.get("angular_upper", "-3/25"))
    )


def run_checks(invoke):
    checks = 0
    def require(condition, description):
        nonlocal checks
        checks += 1
        if not condition:
            raise AssertionError(description)

    requests = []
    for anchor in (LOW[4], Q(10), HIGH[4]):
        for corner in product(("0", "1"), repeat=6):
            requests.append(dict(action="sample", anchor=str(anchor), unit=list(corner)))

    # Arbitrary positive affine normalizers, independent of the physical domain.
    custom = dict(offset=strings(map(Q, ("1", "-8", "9", "1", "-2", "3"))),
                  scale=strings(map(Q, ("3/7", "11/2", "1/1000", "8", "2", "5/9"))))
    rng = random.Random(20261105)
    for i in range(72):
        requests.append(dict(action="sample", anchor="10",
                             unit=strings(Q(rng.randrange(1001), 1000) for _ in range(6)),
                             normalization=custom if i % 2 else dict(
                                 offset=strings(LOW), scale=strings(b-a for a,b in zip(LOW,HIGH))),
                             output=str(Q(1, 2) + (i % 3 - 1) * Q(1, 10**20))))

    # Three simultaneous collapsed coordinates, plus a non-default feasible cap.
    for corner in product(("0", "1"), repeat=6):
        requests.append(dict(action="sample", anchor="0", band_upper="0",
                             velocity_upper=str(LOW[1]), angular_upper=str(LOW[2]), unit=list(corner)))
    requests.append(dict(action="sample", anchor="10", band_upper="3/4",
                         velocity_upper="-9/20", angular_upper="-1/5", unit=["1/3"]*6))

    replies = invoke(requests)
    require(len(replies) == len(requests), "one reply per valid request")
    encoding_requests = []
    for i, (req, reply) in enumerate(zip(requests, replies)):
        require(reply.get("status") == "sampled", f"sample {i} status: {reply}")
        physical = tuple(map(Q, reply["physical"]))
        normalized = tuple(map(Q, reply["normalized"]))
        require(pre(req, physical), f"sample {i}: direct physical precondition")
        offset, scale = normalizer(req)
        require(tuple(z*s+o for z,s,o in zip(normalized,scale,offset)) == physical,
                f"sample {i}: exact normalizer round trip")
        out = Q(181,1000) + Q(12,1000)*Q(req.get("output", "1/2"))
        require(Q(reply["physical_output"]) == out, f"sample {i}: output units")
        require(Q(reply["loss"]) == max(0,out-Q(187,1000)), f"sample {i}: physical hinge loss")
        require(reply["verdict"] == ("satisfied" if out <= Q(187,1000) else "violated"),
                f"sample {i}: output boundary verdict")
        require(reply["precondition"] is True, f"sample {i}: executable predicate")
        enc = {k:v for k,v in req.items() if k not in ("unit", "output")}
        enc.update(action="encode", physical=strings(physical))
        encoding_requests.append(enc)

    encoded = invoke(encoding_requests)
    roundtrip_requests = []
    for i, (req, reply) in enumerate(zip(encoding_requests, encoded)):
        require(reply.get("status") == "encoded", f"encode {i}")
        unit = tuple(map(Q, reply["unit"]))
        require(all(0 <= q <= 1 for q in unit), f"encode {i}: unit cube")
        r = {k:v for k,v in req.items() if k != "physical"}
        r.update(action="sample", unit=strings(unit))
        roundtrip_requests.append(r)
    roundtrips = invoke(roundtrip_requests)
    for i, (first, last) in enumerate(zip(replies, roundtrips)):
        require(last.get("physical") == first["physical"], f"encode/decode {i}: exact recovery")

    # Monitor real witnesses on both sides of each input boundary, no tolerance.
    good = [Q(2),Q(-2,5),Q(-1,5),Q(-4,5),Q(10),Q(-9)]
    monitor_requests = []
    points = [good]
    for index, value in ((1,Q(-3,10)+Q(1,10**20)), (2,Q(-3,25)+Q(1,10**20)),
                         (5,Q(-10)-Q(1,10**20)),(5,Q(-8)+Q(1,10**20)),
                         (0,LOW[0]-Q(1,10**20)),(4,HIGH[4]+Q(1,10**20))):
        p = list(good)
        p[index] = value
        points.append(p)
    for p in points:
        for output in ("1/2", "50000000000000000001/100000000000000000000"):
            z = [(x-a)/(b-a) for x,a,b in zip(p,LOW,HIGH)]
            monitor_requests.append(dict(action="monitor",anchor="10",normalized=strings(z),output=output))
    observations = invoke(monitor_requests)
    for i,(req,reply) in enumerate(zip(monitor_requests,observations)):
        expected = "outside" if not pre(req,points[i//2]) else ("satisfied" if Q(req["output"]) <= Q(1,2) else "violated")
        require(reply.get("verdict") == expected, f"monitor boundary {i}: {reply}")

    base = dict(action="sample",anchor="10",unit=["1/2"]*6)
    rejects = [
        {**base,"band_upper":"-3/10","velocity_upper":"2"}, # actual swapped defaults
        {**base,"anchor":"100"}, {**base,"anchor":"-100"},
        {**base,"velocity_upper":"-1"}, {**base,"angular_upper":"-1"},
        {**base,"unit":["-1/100"]+["0"]*5},
        {**base,"unit":["1001/1000"]+["0"]*5},
        dict(action="encode",anchor="10",physical=strings([Q(0)]*6)),
    ]
    for i,reply in enumerate(invoke(rejects)):
        require(reply.get("status") == "rejected", f"invalid region/unit {i}: {reply}")

    errors = [
        {**base,"unit":["0"]*5}, {**base,"unit":["NaN"]*6},
        {**base,"unit":["1/0"]*6}, {**base,"unit":["0.5"]*6},
        {**base,"unit":[0]*6}, {**base,"bandUpper":"-1"},
        {**base,"output":None}, {**base,"anchor":"infinity"},
        {**base,"normalization":{"offset":["0"]*6,"scale":["0"]*6}},
        {**base,"normalization":{"offset":["0"]*6,"scale":["-1"]*6}},
        {**base,"normalization":{"offset":["0"]*6,"scale":["1"]*6,"ignored":True}},
        {**base,"normalization":None}, {**base,"action":"unknown"},
    ]
    for i,reply in enumerate(invoke(errors)):
        require(reply.get("status") == "error", f"malformed request {i}: {reply}")

    # An independent rational witness of the original double-normalization bug:
    # the first normalized y lower bound is reinterpreted as a physical y.
    wrong_y = (Q(-10)-LOW[5])/(HIGH[5]-LOW[5])
    bad = list(good)
    bad[5] = wrong_y
    bad_normalized = [(x-a)/(b-a) for x,a,b in zip(bad,LOW,HIGH)]
    double = invoke([dict(action="monitor",anchor="10",normalized=strings(bad_normalized),output="1/2")])[0]
    require(not pre({"anchor":"10"},bad), "double normalization witness is outside physical predicate")
    require(double["verdict"] == "outside", "monitor rejects double-normalized region witness")

    # One readable default witness for the saved result.
    bounds = invoke([dict(action="bounds",anchor="10")])[0]
    require(tuple(map(Q,bounds["physical_lo"]))[5] == -10, "default y lower")
    require(tuple(map(Q,bounds["physical_hi"]))[5] == -8, "default y upper")
    require(Q(bounds["physical_hi"][1]) == Q(-3,10), "default vy cap")
    require(Q(bounds["physical_hi"][2]) == Q(-3,25), "default omega cap")
    return dict(assertions=checks, sampled_points=len(requests),
                exact_roundtrips=len(roundtrips), monitor_boundary_cases=len(observations),
                rejected_cases=len(rejects), parser_error_cases=len(errors),
                default_anchor_10_bounds=bounds,
                double_normalization_witness=str(wrong_y))
