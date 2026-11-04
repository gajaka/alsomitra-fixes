"""Two implementation defects, a minimal correction, and separate variants.

Corrected* classes retain the framework's anchor-relative rectangles.
Fixed* legacy names implement the optional, different candidate-coupled region.
The theta discrepancy is an author question rather than a claimed third bug.
"""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys

import numpy as np
import torch

from property_driven_ml.constraints.constraints import AlsomitraProperty2Constraint
from alsomitra_fixes.alsomitra_fix import FixedAlsomitraProperty2Constraint
from alsomitra_fixes.property2_patch import CorrectedAlsomitraProperty2Constraint

DEV = torch.device("cpu")
MIN = torch.tensor([0.967568, -0.607397, -0.356973, -0.968479, 0.482421, -41.681405])
MAX = torch.tensor([3.489893, -0.043021, 0.049180, -0.068003, 41.714717, 4.197234])
V_X, V_Y, OMEGA, THETA, X, Y = range(6)


def sample(n=3000, seed=0):
    g = torch.Generator().manual_seed(seed)
    return torch.rand(n, 6, generator=g)


def denorm(z):
    return z * (MAX - MIN) + MIN


# ---- step 1: reproduce -------------------------------------------------------
def test_upstream_swaps_thresholds():
    # Defect 1: with default arguments, upstream stores 2.0 as the velocity
    # threshold and -0.3 as the band threshold; the intended values are the
    # other way round.
    p = AlsomitraProperty2Constraint(DEV).precondition
    assert p.v_y_threshold == 2.0 and p.y_threshold == -0.3  # intended: -0.3 and 2.0


def test_upstream_reversed_bounds_still_generate_finite_samples():
    # The ordered interval is infeasible. The sampler nevertheless evaluates
    # rand*(hi-lo)+lo and returns points between its reversed endpoints.
    constraint = AlsomitraProperty2Constraint(DEV)
    z = sample()
    lo, hi = constraint.precondition.get_bounds(z)
    assert bool((lo[:, Y] > hi[:, Y]).all())
    candidates = constraint.uniform_sample(z, 1).squeeze(0)
    assert candidates.shape == z.shape and bool(torch.isfinite(candidates).all())
    assert bool(((candidates >= torch.minimum(lo, hi)) &
                 (candidates <= torch.maximum(lo, hi))).all())


def test_upstream_double_normalization_alone():
    """Swap undone but get_bounds kept: the y-interval is still wrongly scaled.

    Defect 2 is isolated from defect 1: the upstream precondition is built
    with the correct thresholds passed by keyword, and the upper y bound still
    disagrees with the value obtained by normalizing the physical bound once.
    """
    from property_driven_ml.constraints.preconditions import AlsomitraProperty2 as P2

    z = sample()
    p = P2(DEV, v_y_threshold=-0.3, y_threshold=2.0, omega_threshold=-0.12)
    _, hi = p.get_bounds(z)
    physical_x = denorm(z)[:, X]
    expected_physical_hi = torch.minimum(2.0 - physical_x, MAX[Y])
    expected_normalized_hi = (expected_physical_hi - MIN[Y]) / (MAX[Y] - MIN[Y])
    assert not torch.allclose(hi[:, Y], expected_normalized_hi)
    # Double normalization also clips both intended caps back to the domain
    # maxima: neither v_y <= -0.3 nor omega <= -0.12 is retained.
    actual_hi = denorm(hi)
    assert torch.allclose(actual_hi[:, V_Y], MAX[V_Y].expand(len(z)), atol=1e-6)
    assert torch.allclose(actual_hi[:, OMEGA], MAX[OMEGA].expand(len(z)), atol=1e-6)
    assert bool((actual_hi[:, V_Y] > -0.3).all())
    assert bool((actual_hi[:, OMEGA] > -0.12).all())


# ---- steps 2-3: fix is correct ----------------------------------------------
def test_corrected_thresholds_preserve_the_intended_binding():
    # Fix for defect 1: each threshold is bound to the intended quantity.
    p = CorrectedAlsomitraProperty2Constraint(DEV).precondition
    assert (p.v_y_threshold, p.y_threshold, p.omega_threshold) == (-0.3, 2.0, -0.12)


def test_corrected_bounds_normalize_once_and_use_the_original_anchor():
    z = sample()
    constraint = CorrectedAlsomitraProperty2Constraint(DEV)
    lo, hi = constraint.precondition.get_bounds(z)
    physical_anchor = denorm(z)
    expected_lo = torch.maximum(-physical_anchor[:, X], MIN[Y])
    expected_hi = torch.minimum(2.0-physical_anchor[:, X], MAX[Y])
    actual_lo, actual_hi = denorm(lo), denorm(hi)
    assert bool((lo <= hi).all())
    assert torch.allclose(actual_lo[:, Y], expected_lo, atol=1e-5)
    assert torch.allclose(actual_hi[:, Y], expected_hi, atol=1e-5)
    assert torch.allclose(actual_hi[:, V_Y], torch.full_like(expected_hi, -0.3), atol=1e-6)
    assert torch.allclose(actual_hi[:, OMEGA], torch.full_like(expected_hi, -0.12), atol=1e-6)


def test_corrected_sampler_keeps_the_framework_anchor_relative_rectangle():
    z = sample(500)
    constraint = CorrectedAlsomitraProperty2Constraint(DEV)
    torch.manual_seed(1701)
    candidates = constraint.uniform_sample(z, 1).squeeze(0)
    physical = denorm(candidates)
    anchor_band = denorm(z)[:, X]+physical[:, Y]
    assert bool(((anchor_band >= -1e-4) & (anchor_band <= 2.0+1e-4)).all())
    assert bool((physical[:, V_Y] <= -0.3+1e-6).all())
    assert bool((physical[:, OMEGA] <= -0.12+1e-6).all())
    own_band = physical[:, X]+physical[:, Y]
    assert float(((own_band < -1e-4) | (own_band > 2.0+1e-4)).float().mean()) > 0.5


def test_minimal_upstream_patch_applies_and_matches_the_local_correction(tmp_path, monkeypatch):
    import property_driven_ml.constraints.preconditions as upstream

    checkout = Path(upstream.__file__).resolve().parents[3]
    relative = Path("src/property_driven_ml/constraints")
    for name in ("preconditions.py", "constraints.py"):
        source, target = checkout/relative/name, tmp_path/relative/name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    patch = Path(__file__).resolve().parents[1]/"upstream_property2.patch"
    checked = subprocess.run(["git", "apply", "--check", str(patch)], cwd=tmp_path,
                             capture_output=True, text=True)
    assert checked.returncode == 0, checked.stderr
    applied = subprocess.run(["git", "apply", str(patch)], cwd=tmp_path,
                             capture_output=True, text=True)
    assert applied.returncode == 0, applied.stderr

    def module(name, filename):
        spec = importlib.util.spec_from_file_location(name, filename)
        result = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(result)
        return result

    pre = module("property_driven_ml.constraints._patched_preconditions",
                 tmp_path/relative/"preconditions.py")
    monkeypatch.setitem(sys.modules, "property_driven_ml.constraints.preconditions", pre)
    con = module("property_driven_ml.constraints._patched_constraints", tmp_path/relative/"constraints.py")
    patched = con.AlsomitraProperty2Constraint(DEV)
    local = CorrectedAlsomitraProperty2Constraint(DEV)
    assert (patched.precondition.v_y_threshold, patched.precondition.y_threshold) == (-0.3, 2.0)
    z = sample(200)
    expected = local.precondition.get_bounds(z)
    actual = patched.precondition.get_bounds(z)
    assert all(torch.equal(a, b) for a, b in zip(actual, expected))
    assert torch.equal(patched.postcondition.hi, local.postcondition.hi)


def test_variant_envelope_and_samples_match_candidate_coupled_conditions():
    # Optional SAIV/global specification, not the framework's local rectangle.
    z = sample()
    constraint = FixedAlsomitraProperty2Constraint(DEV)
    lo, hi = constraint.precondition.get_bounds(z)
    assert bool((lo <= hi).all())
    assert bool((lo >= 0).all()) and bool((hi <= 1).all())
    plo, phi = denorm(lo), denorm(hi)
    candidates = constraint.uniform_sample(z, 1).squeeze(0)
    assert bool(((candidates >= lo) & (candidates <= hi)).all())
    actual = denorm(candidates)
    x = actual[:, X]  # Check the candidate's x, not the original anchor's x.
    exp_lo_y = torch.maximum(-x, MIN[Y])
    exp_hi_y = torch.minimum(2.0 - x, MAX[Y])
    assert bool((actual[:, Y] >= exp_lo_y - 1e-4).all())
    assert bool((actual[:, Y] <= exp_hi_y + 1e-4).all())
    assert bool((actual[:, V_Y] <= -0.3 + 1e-5).all())
    assert bool((actual[:, OMEGA] <= -0.12 + 1e-5).all())
    assert torch.allclose(phi[:, V_Y], torch.full_like(phi[:, V_Y], -0.3), atol=1e-5)
    assert torch.allclose(phi[:, OMEGA], torch.full_like(phi[:, OMEGA], -0.12), atol=1e-5)
    assert torch.allclose(plo[:, V_Y], torch.full_like(plo[:, V_Y], MIN[V_Y]), atol=1e-5)


def test_corrected_output_scale_is_unchanged():
    # The output threshold 0.187 is normalized with the upstream output
    # constants min=0.181, max=0.193; no lower output bound is imposed (NaN).
    post = CorrectedAlsomitraProperty2Constraint(DEV).postcondition
    assert np.isnan(post.lo.item())
    assert abs(post.hi.item() - 0.5) < 1e-3  # (0.187-0.181)/0.012 = 0.5


# ---- distinct rectangular and coupled specifications ------------------------
def test_upstream_property1_respects_its_anchor_band_not_the_global_variant():
    """Independent sampling is consistent with the framework's local box.

    The y bounds of that box are computed from the ANCHOR x
    (y in [-2 - x_anchor, 2 - x_anchor] for Property1), but x itself is then
    redrawn uniformly over its whole domain. The candidate's own x + y is
    therefore not constrained. This is a documented specification difference,
    not a third implementation defect. Property1's band is unaffected by the
    two Property2 implementation defects.
    """
    from property_driven_ml.constraints.constraints import AlsomitraProperty1Constraint

    # The sampling seed must differ from the anchor seed used by sample():
    # with the same seed, torch.rand_like would reproduce the anchor values
    # exactly and hide the specification difference (candidate x = anchor x).
    torch.manual_seed(1701)
    constraint = AlsomitraProperty1Constraint(DEV)
    z = sample(500)
    lo, hi = constraint.precondition.get_bounds(z)
    candidates = constraint.uniform_sample(z, 1).squeeze(0)
    assert bool(((candidates >= lo - 1e-6) & (candidates <= hi + 1e-6)).all())
    anchored_band = denorm(z)[:, X] + denorm(candidates)[:, Y]
    assert bool(((anchored_band >= -2.0-1e-4) & (anchored_band <= 2.0+1e-4)).all())
    band = denorm(candidates)[:, X] + denorm(candidates)[:, Y]
    violating = ((band < -2.0 - 1e-4) | (band > 2.0 + 1e-4)).float().mean().item()
    assert violating > 0.5  # observed about 0.9 for seeds 1, 2, 3 and 1701


def test_variant_sampling_respects_each_candidates_own_band():
    # Optional coupled specification: choose x, then y allowed by THAT x.
    from alsomitra_fixes.alsomitra_fix import FixedAlsomitraProperty1Constraint

    torch.manual_seed(1701)
    constraint = FixedAlsomitraProperty1Constraint(DEV)
    candidates = constraint.uniform_sample(sample(500), 1).squeeze(0)
    band = denorm(candidates)[:, X] + denorm(candidates)[:, Y]
    assert bool(((band >= -2.0 - 1e-4) & (band <= 2.0 + 1e-4)).all())


# ---- Property1: deviation from the paper (SAIV 2025, eq. 23) -----------------
# UNCERTAIN: this documents a discrepancy between the paper and the upstream
# default. It is not claimed to be a defect; the positive bound may be an
# intentional choice by the authors.
def test_upstream_property1_theta_upper_bound_deviates_from_paper():
    """Paper: -0.786 <= theta <= -0.747. Upstream default is (-0.786, +0.747); the
    positive upper bound is clipped to the domain max (-0.068), widening the region."""
    from property_driven_ml.constraints.constraints import AlsomitraProperty1Constraint

    z = sample(200)
    lo, hi = AlsomitraProperty1Constraint(DEV).precondition.get_bounds(z)
    theta_hi = denorm(hi)[:, THETA]
    assert torch.allclose(theta_hi, torch.full_like(theta_hi, MAX[THETA]), atol=1e-4)
    assert not torch.allclose(theta_hi, torch.full_like(theta_hi, -0.747), atol=1e-3)
