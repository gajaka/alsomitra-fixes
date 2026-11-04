"""Tests of the optional candidate-coupled regions and their attack adapter.

These regions are an explicit local/global variant. They do not classify the
framework's anchor-relative rectangular sampling as a third upstream defect.
Floating-point membership checks are numerical guards, not formal certificates.
The attack checks below exercise upstream PGD/APGD without training a network.
"""
from itertools import product

import pytest
import torch

from alsomitra_fixes.alsomitra_fix import (
    AlsomitraAttackAdapter,
    FixedAlsomitraProperty1Constraint,
    FixedAlsomitraProperty2Constraint,
)
from property_driven_ml.constraints.constraints import AlsomitraProperty2Constraint
from property_driven_ml.logics import DL2
from property_driven_ml.training.attacks import APGD, PGD


CPU = torch.device("cpu")
DOMAIN_MIN = (0.967568, -0.607397, -0.356973, -0.968479, 0.482421, -41.681405)
DOMAIN_MAX = (3.489893, -0.043021, 0.049180, -0.068003, 41.714717, 4.197234)
FACTORIES = {"P1": FixedAlsomitraProperty1Constraint, "P2": FixedAlsomitraProperty2Constraint}


def _physical(candidate):
    """Independent default-normalization calculation in binary64."""
    lower = torch.tensor(DOMAIN_MIN, dtype=torch.float64)
    upper = torch.tensor(DOMAIN_MAX, dtype=torch.float64)
    return candidate.detach().to(torch.float64) * (upper - lower) + lower


def _assert_own_region(candidate, property_name, *, band=None, theta=None, vy=None, omega=None):
    # These explicit tolerances cover dtype conversion/normalization only.
    # Unlike calling region.contains, this predicate independently reads the
    # candidate's own physical coordinates and declared property parameters.
    tolerance = 3e-5 if candidate.dtype == torch.float32 else 1e-12
    physical = _physical(candidate)
    lower = torch.tensor(DOMAIN_MIN, dtype=torch.float64)
    upper = torch.tensor(DOMAIN_MAX, dtype=torch.float64)
    assert torch.isfinite(physical).all()
    assert (physical >= lower - tolerance).all()
    assert (physical <= upper + tolerance).all()
    if property_name == "P1":
        band = (-2.0, 2.0) if band is None else band
        theta = (-0.786, -0.747) if theta is None else theta
        assert (physical[..., 3] >= theta[0] - tolerance).all()
        assert (physical[..., 3] <= theta[1] + tolerance).all()
    else:
        band = (0.0, 2.0) if band is None else band
        vy = -0.3 if vy is None else vy
        omega = -0.12 if omega is None else omega
        assert (physical[..., 1] <= vy + tolerance).all()
        assert (physical[..., 2] <= omega + tolerance).all()
    actual_band = physical[..., 4] + physical[..., 5]
    assert (actual_band >= band[0] - tolerance).all()
    assert (actual_band <= band[1] + tolerance).all()


def _cube_points(dtype):
    corners = torch.tensor(list(product((0.0, 1.0), repeat=6)), dtype=dtype)
    interior = torch.rand((37, 6), dtype=dtype, generator=torch.Generator().manual_seed(83))
    return torch.cat((corners, interior), dim=0)


@pytest.mark.parametrize("property_name", FACTORIES)
@pytest.mark.parametrize("dtype", [torch.float32, torch.float64])
def test_variant_decode_encode_corners_and_interior(property_name, dtype):
    region = FACTORIES[property_name](CPU).precondition
    candidate = region.decode(_cube_points(dtype))
    _assert_own_region(candidate, property_name)
    encoded = region.encode(candidate)
    assert ((encoded >= 0) & (encoded <= 1)).all()
    # Collapsed conditional y intervals can have multiple latent encodings;
    # equality is required for decoded network inputs, not for latent points.
    tolerance = 2e-6 if dtype == torch.float32 else 1e-13
    torch.testing.assert_close(region.decode(encoded), candidate, atol=tolerance, rtol=0)
    assert region.contains(candidate).all()


@pytest.mark.parametrize("property_name", FACTORIES)
@pytest.mark.parametrize("dtype", [torch.float32, torch.float64])
def test_variant_projection_and_envelope_use_candidate_coordinates(property_name, dtype):
    region = FACTORIES[property_name](CPU).precondition
    outside = torch.linspace(-4, 5, 18, dtype=dtype).reshape(3, 6)
    projected = region.project(outside)
    _assert_own_region(projected, property_name)
    tolerance = 2e-6 if dtype == torch.float32 else 1e-13
    torch.testing.assert_close(region.project(projected), projected, atol=tolerance, rtol=0)
    lo, hi = region.get_bounds(outside)
    assert lo.shape == outside.shape == hi.shape
    assert ((projected >= lo - tolerance) & (projected <= hi + tolerance)).all()
    # An envelope does not represent the diagonal band exactly: opposite
    # envelope corners need not be feasible candidates.
    assert not region.contains(lo).all() or not region.contains(hi).all()


@pytest.mark.parametrize("property_name", FACTORIES)
def test_variant_sampler_is_reproducible_and_anchor_independent(property_name):
    constraint = FACTORIES[property_name](CPU)
    first = constraint.uniform_sample(
        torch.zeros((5, 6)), 3, generator=torch.Generator().manual_seed(71)
    )
    second = constraint.uniform_sample(
        torch.ones((5, 6)), 3, generator=torch.Generator().manual_seed(71)
    )
    assert first.shape == (3, 5, 6)
    assert torch.equal(first, second)
    _assert_own_region(first, property_name)
    for bad_count in (0, -1, True, 1.5):
        with pytest.raises(ValueError, match="positive integer"):
            constraint.uniform_sample(torch.zeros((1, 6)), bad_count)


@pytest.mark.parametrize("property_name", FACTORIES)
@pytest.mark.parametrize("dtype", [torch.float32, torch.float64])
def test_variant_zero_width_bands_and_coordinate_caps(property_name, dtype):
    if property_name == "P1":
        constraint = FACTORIES[property_name](CPU, y_threshold=0, theta_threshold=(-0.786, -0.786))
        caps = {"band": (0, 0), "theta": (-0.786, -0.786)}
        collapsed = (3, 5)
    else:
        constraint = FACTORIES[property_name](
            CPU, y_threshold=0, v_y_threshold=DOMAIN_MIN[1], omega_threshold=DOMAIN_MIN[2]
        )
        caps = {"band": (0, 0), "vy": DOMAIN_MIN[1], "omega": DOMAIN_MIN[2]}
        collapsed = (1, 2, 5)
    region = constraint.precondition
    candidate = region.decode(_cube_points(dtype))
    _assert_own_region(candidate, property_name, **caps)
    encoded = region.encode(candidate)
    assert (encoded[:, collapsed] == 0).all()
    assert torch.isfinite(encoded).all()
    tolerance = 2e-6 if dtype == torch.float32 else 1e-13
    torch.testing.assert_close(region.decode(encoded), candidate, atol=tolerance, rtol=0)


@pytest.mark.parametrize("property_name", FACTORIES)
def test_variant_custom_thresholds_are_applied_to_the_right_coordinates(property_name):
    if property_name == "P1":
        constraint = FACTORIES[property_name](CPU, y_threshold=0.5, theta_threshold=(-0.8, -0.75))
        caps = {"band": (-0.5, 0.5), "theta": (-0.8, -0.75)}
    else:
        constraint = FACTORIES[property_name](
            CPU, y_threshold=0.75, v_y_threshold=-0.45, omega_threshold=-0.2
        )
        caps = {"band": (0, 0.75), "vy": -0.45, "omega": -0.2}
    _assert_own_region(constraint.precondition.decode(_cube_points(torch.float64)), property_name, **caps)


@pytest.mark.parametrize("property_name,kwargs", [
    ("P1", {"y_threshold": -1}),
    ("P1", {"theta_threshold": (-0.7, -0.8)}),
    ("P1", {"theta_threshold": (1.0, 2.0)}),
    ("P1", {"theta_threshold": (-0.8, float("nan"))}),
    ("P2", {"y_threshold": -1}),
    ("P2", {"y_threshold": float("inf")}),
    ("P2", {"v_y_threshold": -1.0}),
    ("P2", {"omega_threshold": -1.0}),
    ("P2", {"v_y_threshold": float("nan")}),
])
def test_variant_invalid_or_infeasible_thresholds_are_rejected(property_name, kwargs):
    with pytest.raises(ValueError):
        FACTORIES[property_name](CPU, **kwargs)


def test_variant_membership_tolerance_is_explicit_and_not_a_certificate():
    region = FixedAlsomitraProperty1Constraint(CPU).precondition
    physical = torch.tensor([[2.0, -0.4, -0.15, -0.7665, 2.0, 1e-5]], dtype=torch.float32)
    candidate = region.normalize(physical)
    # The point is strictly outside the own-candidate band. Default float32
    # tolerance can accept it; this is why contains is not called a proof.
    assert _physical(candidate)[0, 4:].sum() > 2
    assert region.contains(candidate).item()
    assert not region.contains(candidate, atol=0).item()
    assert region.contains(candidate, atol=2e-5).item()
    for invalid in (-1, float("nan"), float("inf")):
        with pytest.raises(ValueError):
            region.contains(candidate, atol=invalid)


@pytest.mark.parametrize("property_name", FACTORIES)
def test_variant_decode_preserves_the_coupled_autograd_path(property_name):
    region = FACTORIES[property_name](CPU).precondition
    unit = torch.full((2, 6), 0.5, dtype=torch.float64, requires_grad=True)
    physical = region.denormalize(region.decode(unit))
    y_gradient = torch.autograd.grad(physical[:, 5].sum(), unit, retain_graph=True)[0]
    band_gradient = torch.autograd.grad(physical[:, 4:].sum(), unit)[0]
    assert torch.isfinite(y_gradient).all()
    assert (y_gradient[:, 4] < -1).all()  # Changing x changes the conditional y.
    torch.testing.assert_close(band_gradient[:, 4], torch.zeros(2, dtype=unit.dtype), atol=1e-12, rtol=0)
    assert (band_gradient[:, 5] > 0).all()


def test_variant_invalid_inputs_fail_before_arithmetic_or_loss_evaluation():
    constraint = FixedAlsomitraProperty2Constraint(CPU)
    region = constraint.precondition
    invalid = [torch.zeros(2, 5), torch.zeros(2, 6, dtype=torch.int64),
               torch.full((2, 6), float("nan")), torch.full((2, 6), float("inf"))]
    for candidate in invalid:
        for operation in (region.decode, region.encode, region.project, region.contains):
            with pytest.raises(ValueError):
                operation(candidate)
    with pytest.raises(ValueError, match="unit cube"):
        region.decode(torch.full((2, 6), 1.01))
    with pytest.raises(ValueError, match="outside"):
        region.encode(torch.ones((2, 6)))
    with pytest.raises(ValueError, match="precondition"):
        constraint.eval(torch.nn.Linear(6, 1), torch.zeros((2, 6)), torch.ones((2, 6)), None, DL2())


class _ProbeModel(torch.nn.Module):
    def __init__(self, dtype=torch.float32, fail=False):
        super().__init__()
        self.layers = torch.nn.Sequential(
            torch.nn.Linear(6, 6), torch.nn.BatchNorm1d(6),
            torch.nn.Dropout(0.5), torch.nn.Linear(6, 1),
        ).to(dtype=dtype)
        with torch.no_grad():
            self.layers[0].weight.fill_(0.1)
            self.layers[0].bias.fill_(0.1)
            self.layers[3].weight.fill_(0.2)
            self.layers[3].bias.fill_(0.8)
        # Deliberately mixed original flags. Restoring only the top-level
        # training flag would lose this state.
        self.train()
        self.layers[2].eval()
        self.seen = []
        self.gradients = []
        self.fail = fail

    def forward(self, candidate):
        assert all(not module.training for module in self.modules())
        self.seen.append(candidate.detach().clone())
        if candidate.requires_grad:
            candidate.register_hook(lambda gradient: self.gradients.append(gradient.detach().clone()))
        if self.fail:
            raise RuntimeError("intentional model failure")
        return self.layers(candidate)


def _oracle(attack_name, **kwargs):
    arguments = dict(logic=DL2(), device=CPU, steps=3, restarts=0, **kwargs)
    if attack_name == "PGD":
        return PGD(**arguments, step_size=0.1)
    return APGD(**arguments)


@pytest.mark.parametrize("property_name", FACTORIES)
@pytest.mark.parametrize("attack_name,batch_size,dtype", [
    ("PGD", 1, torch.float32), ("PGD", 2, torch.float32),
    ("PGD", 2, torch.float64), ("APGD", 1, torch.float32),
    ("APGD", 2, torch.float32),
])
def test_variant_actual_upstream_attacks_return_feasible_inputs_and_restore_model(property_name, attack_name, batch_size, dtype):
    with torch.random.fork_rng():
        torch.manual_seed(29)
        constraint = FACTORIES[property_name](CPU)
        model = _ProbeModel(dtype)
        before_modes = [module.training for module in model.modules()]
        before_state = {name: value.clone() for name, value in model.state_dict().items()}
        oracle = _oracle(attack_name)
        adapter = AlsomitraAttackAdapter(oracle)
        # An infeasible data anchor is accepted: projection is part of the
        # adapter, while every actual network evaluation must be feasible.
        anchor = torch.ones((batch_size, 6), dtype=dtype)
        with torch.no_grad():
            adversarial = adapter.attack(model, anchor, torch.zeros((batch_size, 1), dtype=dtype), constraint)
        assert adversarial.shape == anchor.shape
        assert adversarial.dtype == dtype
        assert not adversarial.requires_grad
        _assert_own_region(adversarial, property_name)
        assert model.seen
        for candidate in model.seen:
            _assert_own_region(candidate, property_name)
        assert model.gradients and any((gradient != 0).any() for gradient in model.gradients)
        assert all(torch.isfinite(gradient).all() for gradient in model.gradients)
        assert [module.training for module in model.modules()] == before_modes
        assert all(torch.equal(before_state[name], value) for name, value in model.state_dict().items())
        assert all(parameter.grad is None for parameter in model.parameters())
        assert not hasattr(oracle, "ndim")  # Cached bounds belong to the call's copy.
        assert adapter.logic is oracle.logic


@pytest.mark.parametrize("attack_name", ["PGD", "APGD"])
def test_variant_attack_restores_mixed_model_flags_after_exception(attack_name):
    model = _ProbeModel(fail=True)
    before_modes = [module.training for module in model.modules()]
    adapter = AlsomitraAttackAdapter(_oracle(attack_name))
    with pytest.raises(RuntimeError, match="intentional model failure"):
        adapter.attack(model, torch.zeros((2, 6)), torch.zeros((2, 1)), FixedAlsomitraProperty2Constraint(CPU))
    assert [module.training for module in model.modules()] == before_modes


def test_variant_attack_rejects_incompatible_oracles_constraints_and_dtypes():
    for kwargs in ({"mean": (0.1,)}, {"std": (2.0,)}):
        with pytest.raises(ValueError, match="mean=0 and std=1"):
            AlsomitraAttackAdapter(_oracle("PGD", **kwargs))
    with pytest.raises(TypeError, match="PGD or APGD"):
        AlsomitraAttackAdapter(object())
    adapter = AlsomitraAttackAdapter(_oracle("PGD"))
    with pytest.raises(TypeError, match="relational"):
        adapter.attack(_ProbeModel(), torch.zeros((2, 6)), None, AlsomitraProperty2Constraint(CPU))
    adapter = AlsomitraAttackAdapter(_oracle("APGD"))
    with pytest.raises(ValueError, match="float32"):
        adapter.attack(_ProbeModel(torch.float64), torch.zeros((2, 6), dtype=torch.float64), None, FixedAlsomitraProperty2Constraint(CPU))
    with pytest.raises(ValueError, match="nonempty batch"):
        adapter.attack(_ProbeModel(), torch.zeros((0, 6)), None, FixedAlsomitraProperty2Constraint(CPU))
