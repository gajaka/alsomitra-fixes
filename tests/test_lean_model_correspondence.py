"""Check that the Lean model computes what the Python code computes.

The Lean files in ``lean/AlsomitraFixes`` prove statements about a real-number
model of the code. This file manually transcribes each model function into
Python (same formulas and decimal literals, evaluated in floating point)
and compares it with the actual upstream and local variant code on
sampled inputs. Agreement here is evidence, not proof, that the model matches
the code; it is only as strong as the sampled inputs and the transcription.
These tests do not execute or parse Lean definitions, and would not detect a
change made only to the Lean source. Lean compilation is a separate check.
"""
import torch

from property_driven_ml.constraints.constraints import (
    AlsomitraProperty1Constraint,
    AlsomitraProperty2Constraint,
)
from property_driven_ml.constraints.preconditions import AlsomitraProperty2
from alsomitra_fixes.alsomitra_fix import FixedAlsomitraProperty1, FixedAlsomitraProperty2

DEV = torch.device("cpu")
X, Y = 4, 5

# Decimal literals from Lean `Defs.lean`, rounded here to binary64.
X_MIN, X_MAX = 0.482421, 41.714717
Y_MIN, Y_MAX = -41.681405, 4.197234
D_MIN = torch.tensor([0.967568, -0.607397, -0.356973, -0.968479, X_MIN, Y_MIN], dtype=torch.float64)
D_MAX = torch.tensor([3.489893, -0.043021, 0.049180, -0.068003, X_MAX, Y_MAX], dtype=torch.float64)

# Upstream stores its domain as float32, so agreement is checked to float32 precision.
ATOL = 1e-5


def ny(t):
    return (t - Y_MIN) / (Y_MAX - Y_MIN)


def up_lo(xa):  # Lean `upLo`
    return ny(torch.clamp(ny(-xa), min=Y_MIN))


def up_hi(yth, xa):  # Lean `upHi`
    return ny(torch.clamp(ny(yth - xa), max=Y_MAX))


def intended_hi(xa):  # Lean `intendedHi`
    return ny(torch.clamp(2.0 - xa, max=Y_MAX))


C = -Y_MIN / (Y_MAX - Y_MIN - 1)  # Lean `c`


def anchors(n=2000, seed=11):
    g = torch.Generator().manual_seed(seed)
    return torch.rand(n, 6, generator=g, dtype=torch.float64)


def physical_x(z):
    return (z * (D_MAX - D_MIN) + D_MIN)[:, X]


def test_model_upLo_upHi_match_upstream_defaults():
    z = anchors()
    lo, hi = AlsomitraProperty2Constraint(DEV).precondition.get_bounds(z)
    xa = physical_x(z)
    assert torch.allclose(lo[:, Y].double(), up_lo(xa), atol=ATOL)
    assert torch.allclose(hi[:, Y].double(), up_hi(-0.3, xa), atol=ATOL)


def test_model_upHi_matches_upstream_with_correct_threshold():
    z = anchors()
    p = AlsomitraProperty2(DEV, v_y_threshold=-0.3, y_threshold=2.0, omega_threshold=-0.12)
    _, hi = p.get_bounds(z)
    assert torch.allclose(hi[:, Y].double(), up_hi(2.0, physical_x(z)), atol=ATOL)


def test_exceptional_anchor_is_the_only_agreement_point():
    # Lean `defect2_hi_agrees_iff`: agreement exactly at xa = 2 - c.
    xa_star = torch.tensor([2.0 - C], dtype=torch.float64)
    assert torch.allclose(up_hi(2.0, xa_star), intended_hi(xa_star), atol=1e-12)
    others = torch.linspace(X_MIN, X_MAX, 400, dtype=torch.float64)
    others = others[(others - (2.0 - C)).abs() > 0.1]
    assert bool(((up_hi(2.0, others) - intended_hi(others)).abs() > 1e-3).all())


def test_model_UpstreamBox1_matches_upstream_property1_bounds():
    # Lean `UpstreamBox1`: x over its whole domain, y in clipped [-2-xa, 2-xa].
    z = anchors()
    lo, hi = AlsomitraProperty1Constraint(DEV).precondition.get_bounds(z)
    xa = physical_x(z)
    y_lo = torch.clamp(-2.0 - xa, min=Y_MIN)
    y_hi = torch.clamp(2.0 - xa, max=Y_MAX)
    norm_y = lambda t: (t - Y_MIN) / (Y_MAX - Y_MIN)
    assert torch.allclose(lo[:, X].double(), torch.zeros_like(xa), atol=ATOL)
    assert torch.allclose(hi[:, X].double(), torch.ones_like(xa), atol=ATOL)
    assert torch.allclose(lo[:, Y].double(), norm_y(y_lo), atol=ATOL)
    assert torch.allclose(hi[:, Y].double(), norm_y(y_hi), atol=ATOL)


def lean_decode(u, v, bl, bh):  # Lean `Coupled.decodeX` / `decodeY`
    x_lo = max(X_MIN, bl - Y_MAX)
    x_hi = min(X_MAX, bh - Y_MIN)
    x = x_lo + u * (x_hi - x_lo)
    y_lo = torch.clamp(bl - x, min=Y_MIN)
    y_hi = torch.clamp(bh - x, max=Y_MAX)
    return x, y_lo + v * (y_hi - y_lo)


def check_decode(region, bl, bh):
    unit = anchors(seed=29)
    physical = region.denormalize(region.decode(unit))
    x, y = lean_decode(unit[:, X], unit[:, Y], bl, bh)
    assert torch.allclose(physical[:, X], x, atol=1e-9)
    assert torch.allclose(physical[:, Y], y, atol=1e-9)


def test_model_decode_matches_fixed_property1():
    check_decode(FixedAlsomitraProperty1(DEV), -2.0, 2.0)  # Lean `region1`


def test_model_decode_matches_fixed_property2():
    check_decode(FixedAlsomitraProperty2(DEV), 0.0, 2.0)  # Lean `region2`
