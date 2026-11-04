"""Optional coupled Alsomitra variants; upstream @ 616df1e is unchanged.

Property1 implements Eq. 23 of Kessler et al., SAIV 2025 (arXiv:2505.00622),
including its negative upper pitch bound. Property2 implements Eq. 24. The
paper's property numbers are 3 and 4, respectively. These are explicit local
variants, not a claim that the upstream experiments used these definitions.
The framework paper (arXiv:2505.00466v2, Appendix A.3) deliberately uses anchor-
relative rectangles. Replacing those with candidate-coupled bands changes the
specification, not just an implementation bug. For the two minimal bug fixes
without that change, use ``alsomitra_fixes.property2_patch``.

The coupled input regions are parameterized by a unit cube: choose x first,
then y within the interval permitted by that same x. Sequential sampling is
not generally uniform with respect to volume in the physical region.
"""
from __future__ import annotations

from copy import copy
from math import isfinite

import numpy as np
import torch

from property_driven_ml.constraints.constraints import Constraint
from property_driven_ml.constraints.postconditions import AlsomitraOutputPostcondition
from property_driven_ml.constraints.preconditions import AlsomitraBase, Precondition
from property_driven_ml.training.attacks import APGD, PGD
from alsomitra_fixes.normalization import as_contract


# Six-decimal physical domain from upstream AlsomitraBase. Keep these decimals
# before dtype conversion so a cap equal to a domain endpoint stays feasible.
_DOMAIN_MIN = (0.967568, -0.607397, -0.356973, -0.968479, 0.482421, -41.681405)
_DOMAIN_MAX = (3.489893, -0.043021, 0.049180, -0.068003, 41.714717, 4.197234)


def _finite_number(value, name):
    value = float(value)
    if not isfinite(value):
        raise ValueError(f"{name} must be finite")
    return value


class _AlsomitraRegion(AlsomitraBase):
    """Domain intersection with band_lo <= x+y <= band_hi and coordinate caps.

    ``contains`` has a documented floating-point tolerance by default. It is a
    numerical guard, not a formal certificate over reals or binary64 programs.
    """

    def __init__(self, device, band_lo, band_hi, lower_caps=(), upper_caps=(), *, normalization=None):
        super().__init__(device)
        self.normalization_contract = as_contract(normalization) if normalization is not None else None
        self.band_lo = _finite_number(band_lo, "band_lo")
        self.band_hi = _finite_number(band_hi, "band_hi")
        if self.band_lo > self.band_hi:
            raise ValueError("The x+y band is empty")
        self._domain_min = torch.tensor(_DOMAIN_MIN, dtype=torch.float64)
        self._domain_max = torch.tensor(_DOMAIN_MAX, dtype=torch.float64)
        if self.normalization_contract is not None:
            self._normalization_min = torch.tensor(self.normalization_contract.input_min, dtype=torch.float64)
            self._normalization_scale = torch.tensor(self.normalization_contract.input_scale, dtype=torch.float64)
        public_dtype = torch.float32 if torch.device(device).type == "mps" else torch.float64
        self.min = self._domain_min.to(device=device, dtype=public_dtype)
        self.max = self._domain_max.to(device=device, dtype=public_dtype)
        self._lower = self._domain_min.clone()
        self._upper = self._domain_max.clone()
        for index, value in lower_caps:
            self._lower[index] = max(self._lower[index].item(), value)
        for index, value in upper_caps:
            self._upper[index] = min(self._upper[index].item(), value)
        # Exclude x positions for which the conditional y interval is empty.
        self._lower[self.x] = max(
            self._lower[self.x].item(), self.band_lo - self._upper[self.y].item()
        )
        self._upper[self.x] = min(
            self._upper[self.x].item(), self.band_hi - self._lower[self.y].item()
        )
        if bool((self._lower > self._upper).any()):
            raise ValueError("The property has an empty intersection with the domain")

    @staticmethod
    def _check_tensor(z):
        if not isinstance(z, torch.Tensor) or z.ndim < 1 or z.shape[-1] != 6:
            raise ValueError("Expected a floating tensor with final dimension 6")
        if z.dtype not in (torch.float32, torch.float64) or not bool(torch.isfinite(z).all()):
            raise ValueError("Inputs must be finite float32 or float64 values")

    def _domain(self, like):
        return self._domain_min.to(like), self._domain_max.to(like)

    def _limits(self, like):
        return self._lower.to(like), self._upper.to(like)

    def _normalization(self, like):
        if self.normalization_contract is None:
            minimum, maximum = self._domain(like)
            return minimum, maximum - minimum
        return self._normalization_min.to(like), self._normalization_scale.to(like)

    def _physical(self, z):
        minimum, scale = self._normalization(z)
        return z * scale + minimum

    def _normalized(self, physical):
        minimum, scale = self._normalization(physical)
        return (physical - minimum) / scale

    def normalize(self, physical):
        self._check_tensor(physical)
        return self._normalized(physical)

    def denormalize(self, normalized):
        self._check_tensor(normalized)
        return self._physical(normalized)

    def _y_limits(self, physical_x, lower, upper):
        return (
            torch.maximum(lower[self.y], self.band_lo - physical_x),
            torch.minimum(upper[self.y], self.band_hi - physical_x),
        )

    def decode(self, unit):
        """Map cube coordinates to actual normalized inputs, x first then y.

        The map is differentiable almost everywhere. In particular, changing
        latent x also changes the conditional y interval.
        """
        # VARIANT: unlike the framework's anchor-relative rectangle, this
        # specification constrains each candidate's own x+y. Choose x first
        # and derive y's interval from THAT SAME x. Independent sampling in
        # the upstream anchor rectangle is correct for its declared local
        # specification, but does not enforce this different coupled region.
        # UNCERTAIN: choosing x uniformly and then y uniformly inside its
        # conditional interval is NOT uniform with respect to volume in the
        # physical region (x values with a wider y-interval are
        # under-represented per unit volume). This is fine for producing
        # feasible points, but I have not established that it is the right
        # distribution for training; the authors may intend something else.
        self._check_tensor(unit)
        if bool(((unit < 0) | (unit > 1)).any()):
            raise ValueError("Latent inputs must lie in the unit cube")
        lower, upper = self._limits(unit)
        physical = lower + unit * (upper - lower)
        y_lo, y_hi = self._y_limits(physical[..., self.x], lower, upper)
        physical_y = y_lo + unit[..., self.y] * (y_hi - y_lo)
        coordinates = [physical[..., i] for i in range(6)]
        coordinates[self.y] = physical_y
        return self._normalized(torch.stack(coordinates, dim=-1))

    def encode(self, candidate):
        """Inverse cube coordinates, with zero chosen on collapsed intervals."""
        self._check_tensor(candidate)
        if not bool(self.contains(candidate).all()):
            raise ValueError("Cannot encode a candidate outside the property region")
        physical = self._physical(candidate)
        lower, upper = self._limits(candidate)
        width = upper - lower
        unit = (physical - lower) / torch.where(width > 0, width, 1)
        unit = torch.where(width > 0, unit, 0)
        y_lo, y_hi = self._y_limits(physical[..., self.x], lower, upper)
        y_width = y_hi - y_lo
        y_unit = (physical[..., self.y] - y_lo) / torch.where(y_width > 0, y_width, 1)
        coordinates = [unit[..., i] for i in range(6)]
        coordinates[self.y] = torch.where(y_width > 0, y_unit, 0)
        return torch.stack(coordinates, dim=-1).clamp(0, 1)

    def project(self, candidate):
        """Clamp x, then y using that x; no nearest-point claim is made."""
        self._check_tensor(candidate)
        lower, upper = self._limits(candidate)
        physical = torch.minimum(torch.maximum(self._physical(candidate), lower), upper)
        y_lo, y_hi = self._y_limits(physical[..., self.x], lower, upper)
        coordinates = [physical[..., i] for i in range(6)]
        coordinates[self.y] = torch.minimum(
            torch.maximum(physical[..., self.y], y_lo), y_hi
        )
        return self._normalized(torch.stack(coordinates, dim=-1))

    def contains(self, candidate, atol=None):
        """Check this candidate's coordinates and its own x+y.

        Default coordinate tolerances are 8*eps times the magnitude of the
        normalization terms; band tolerance is the sum for x and y. Explicit
        ``atol`` is a nonnegative physical-unit tolerance for each comparison.
        """
        self._check_tensor(candidate)
        physical = self._physical(candidate)
        lower, upper = self._limits(candidate)
        # UNCERTAIN (numerical tolerance, a modelling choice and not a bug fix):
        # Membership is tested with a small floating-point tolerance, because
        # decode/normalize round-trips in float32 can land a hair outside a
        # boundary that is exactly feasible in real arithmetic. The default
        # tolerance (8 * machine epsilon scaled by the normalization terms) is
        # my choice, not something taken from the paper or upstream. This is a
        # numerical guard only; it is NOT a proof that a point lies in the
        # region over the reals.
        if atol is None:
            minimum, scale = self._normalization(candidate)
            tolerance = 8 * torch.finfo(candidate.dtype).eps * (
                minimum.abs() + scale.abs()
            ).clamp_min(1)
            band_tolerance = tolerance[self.x] + tolerance[self.y]
        else:
            atol = _finite_number(atol, "atol")
            if atol < 0:
                raise ValueError("atol must be nonnegative")
            tolerance = candidate.new_full((6,), atol)
            band_tolerance = atol
        coordinate_ok = (
            (physical >= lower - tolerance) & (physical <= upper + tolerance)
        ).all(-1)
        band = physical[..., self.x] + physical[..., self.y]
        return coordinate_ok & (band >= self.band_lo - band_tolerance) & (
            band <= self.band_hi + band_tolerance
        )

    def get_bounds(self, anchor):
        """Return a bounding box, not an exact representation of the region.

        Use ``decode``/``project`` for feasible points and the attack adapter
        for upstream oracles. The anchor supplies shape, dtype and device;
        its x coordinate does not define this region.
        """
        self._check_tensor(anchor)
        lower, upper = self._limits(anchor)
        lower, upper = lower.clone(), upper.clone()
        # FIX (upstream defect 2, bounds normalized twice): upstream get_bounds
        # normalizes the bounds and then hands them to apply_domain_bounds,
        # which interprets them as physical values and normalizes AGAIN, so
        # the y-interval ends up wrongly scaled even once defect 1 is fixed.
        # Here every limit (lower, upper, and the y-interval derived from the
        # x+y band) is computed in PHYSICAL units first, and converted to
        # normalized units exactly once, in the return statement below.
        lower[self.y] = max(lower[self.y].item(), self.band_lo - upper[self.x].item())
        upper[self.y] = min(upper[self.y].item(), self.band_hi - lower[self.x].item())
        return (
            self._normalized(lower).expand_as(anchor).clone(),
            self._normalized(upper).expand_as(anchor).clone(),
        )


class FixedAlsomitraProperty1(_AlsomitraRegion):
    def __init__(self, device, y_threshold=2.0, theta_thresholds=(-0.786, -0.747), *, normalization=None):
        self.y_threshold = _finite_number(y_threshold, "y_threshold")
        if self.y_threshold < 0:
            raise ValueError("y_threshold must be nonnegative")
        theta_lo, theta_hi = (
            _finite_number(t, "theta threshold") for t in theta_thresholds
        )
        if theta_lo > theta_hi:
            raise ValueError("The theta interval is empty")
        self.theta_thresholds = (theta_lo, theta_hi)
        # UNCERTAIN (possible specification discrepancy, NOT a confirmed bug):
        # The paper (SAIV 2025, Eq. 23) states -0.786 <= theta <= -0.747, i.e.
        # a NEGATIVE upper bound, and that is what this local variant uses.
        # The upstream default is (-0.786, +0.747), a POSITIVE upper bound,
        # which upstream then clips to the domain maximum (-0.068), giving a
        # wider region. I cannot tell whether the positive sign is a typo or
        # an intentional choice by the authors, so this is reported as a
        # discrepancy to be confirmed, not as a defect.
        super().__init__(
            device, -self.y_threshold, self.y_threshold,
            lower_caps=((3, theta_lo),), upper_caps=((3, theta_hi),),
            normalization=normalization,
        )


class FixedAlsomitraProperty2(_AlsomitraRegion):
    def __init__(self, device, v_y_threshold=-0.3, y_threshold=2.0, omega_threshold=-0.12, *, normalization=None):
        self.y_threshold = _finite_number(y_threshold, "y_threshold")
        self.v_y_threshold = _finite_number(v_y_threshold, "v_y_threshold")
        self.omega_threshold = _finite_number(omega_threshold, "omega_threshold")
        if self.y_threshold < 0:
            raise ValueError("y_threshold must be nonnegative")
        # FIX (upstream defect 1, continued): the thresholds are bound to the
        # right quantities here. The x+y band is [0, y_threshold] = [0, 2.0];
        # v_y is capped above by v_y_threshold (-0.3, index 1) and omega by
        # omega_threshold (-0.12, index 2). In upstream the two values land in
        # each other's place, which yields an infeasible ordered band [0, -0.3].
        # Upstream still samples finite points between the reversed endpoints.
        super().__init__(
            device, 0, self.y_threshold,
            upper_caps=((1, self.v_y_threshold), (2, self.omega_threshold)),
            normalization=normalization,
        )


class _RelationalConstraint(Constraint):
    def uniform_sample(self, x, num_samples, *, generator=None):
        # VARIANT: replace the correctly anchor-relative upstream sampler
        # with a different, candidate-coupled specification. This is not a
        # third implementation defect. The unit-cube map chooses x, then y
        # allowed by that same x. The supplied anchor provides shape, dtype
        # and device only; its x does not determine this optional region.
        self.precondition._check_tensor(x)
        if not isinstance(num_samples, int) or isinstance(num_samples, bool) or num_samples <= 0:
            raise ValueError("num_samples must be a positive integer")
        unit = torch.rand(
            (num_samples, *x.shape), device=x.device, dtype=x.dtype, generator=generator
        )
        return self.precondition.decode(unit)

    def eval(self, N, x, x_adv, y_target, logic, reduction=None, skip_sat=False,
             is_attack=False, postcondition_kwargs=None):
        # VARIANT: enforce this optional coupled region. Upstream's local
        # rectangle is a different precondition and does not require this
        # own-coordinate test.
        if x_adv is not None and not bool(self.precondition.contains(x_adv).all()):
            raise ValueError("The candidate violates the coupled Alsomitra precondition")
        return super().eval(
            N, x, x_adv, y_target, logic, reduction=reduction, skip_sat=skip_sat,
            is_attack=is_attack, postcondition_kwargs=postcondition_kwargs or {},
        )


class _ContractOutputPostcondition(AlsomitraOutputPostcondition):
    """Normalize physical loss thresholds using the same frozen data statistics."""

    def __init__(self, device, lo, hi, normalization):
        contract = as_contract(normalization)
        self.device = device
        self.min, self.max, self.scale = contract.output_min, contract.output_max, contract.output_scale
        self.normalization_contract = contract
        # Convert physical thresholds before casting to the training dtype.
        self.lo = torch.tensor((float(lo) - self.min) / self.scale, device=device, dtype=torch.float32)
        self.hi = torch.tensor((float(hi) - self.min) / self.scale, device=device, dtype=torch.float32)

    def normalize(self, y):
        return (y - self.min) / self.scale

    def denormalize(self, y):
        return y * self.scale + self.min


class FixedAlsomitraProperty1Constraint(_RelationalConstraint):
    """Paper Eq. 23 variant with the explicitly selected negative theta bound."""

    # UNCERTAIN (possible specification discrepancy, NOT a confirmed bug):
    # the default theta interval here is (-0.786, -0.747), as written in the
    # paper (SAIV 2025, Eq. 23). Upstream AlsomitraProperty1Constraint uses
    # (-0.786, 0.747); its positive upper bound is then clipped to the domain
    # maximum -0.068, so upstream trains on a wider theta range than the paper
    # states. Whether +0.747 is a sign typo or an intended choice is for the
    # authors to confirm; pass theta_threshold explicitly to reproduce either.
    def __init__(self, device, y_threshold=2.0, theta_threshold=(-0.786, -0.747),
                 bounds_output=(0.184, 0.19), *, normalization=None):
        super().__init__(device)
        self.precondition = FixedAlsomitraProperty1(device, y_threshold, theta_threshold, normalization=normalization)
        self.postcondition = (
            AlsomitraOutputPostcondition(device, *bounds_output) if normalization is None
            else _ContractOutputPostcondition(device, *bounds_output, normalization)
        )


class FixedAlsomitraProperty2Constraint(_RelationalConstraint):
    def __init__(self, device, y_threshold=2.0, v_y_threshold=-0.3,
                 omega_threshold=-0.12, bounds_output=(np.nan, 0.187), *, normalization=None):
        super().__init__(device)
        # FIX (upstream defect 1, swapped constructor arguments):
        # Upstream AlsomitraProperty2Constraint passes y_threshold positionally
        # into the slot where the precondition expects v_y_threshold, so with
        # the defaults v_y_threshold becomes 2.0 and y_threshold becomes -0.3.
        # That makes the declared ordered y-interval empty; the original
        # sampler still generates finite points between reversed endpoints.
        # Here every threshold is passed BY KEYWORD, so the order of the
        # arguments can no longer be confused. Defaults are the intended
        # values: v_y_threshold = -0.3, y_threshold = 2.0, omega = -0.12.
        self.precondition = FixedAlsomitraProperty2(
            device, v_y_threshold=v_y_threshold, y_threshold=y_threshold,
            omega_threshold=omega_threshold,
            normalization=normalization,
        )
        self.postcondition = (
            AlsomitraOutputPostcondition(device, *bounds_output) if normalization is None
            else _ContractOutputPostcondition(device, *bounds_output, normalization)
        )


class _UnitCube(Precondition):
    def get_bounds(self, x):
        return torch.zeros_like(x), torch.ones_like(x)


class _BatchPostcondition:
    """Retain a batch axis of length one for upstream APGD bookkeeping."""

    def __init__(self, postcondition):
        self.postcondition = postcondition

    def build_postcondition(self, N, x_adv):
        evaluate = self.postcondition.build_postcondition(N, x_adv)
        return lambda logic: evaluate(logic).reshape(x_adv.shape[0])


class _CubeConstraint(Constraint):
    def __init__(self, real_constraint):
        super().__init__(real_constraint.device)
        self.precondition = _UnitCube()
        self.postcondition = _BatchPostcondition(real_constraint.postcondition)


class _DecodedModel(torch.nn.Module):
    def __init__(self, model, region, dtype):
        super().__init__()
        self.model, self.region, self.input_dtype = model, region, dtype

    def train(self, mode=True):
        # Upstream attacks call train(True); keep the actual model in eval mode
        # so adversarial search cannot update BatchNorm statistics or use dropout.
        if not isinstance(mode, bool):
            raise ValueError("training mode must be a boolean")
        self.training = mode
        return self

    def forward(self, unit):
        candidate = self.region.decode(unit.to(dtype=self.input_dtype))
        if not bool(self.region.contains(candidate).all()):
            raise ValueError("Decoded attack input is outside the property region")
        return self.model(candidate)


class AlsomitraAttackAdapter:
    """Run upstream PGD/APGD on cube coordinates; return actual network inputs.

    Inputs use mean=0, std=1. PGD accepts float32/64; upstream APGD requires
    float32. Each call copies the oracle and clears its cached domain bounds.
    The model uses eval mode during search, with all original flags restored
    even on exceptions. Autograd remains enabled for adversarial search.
    """

    def __init__(self, oracle):
        if not isinstance(oracle, (PGD, APGD)):
            raise TypeError("Expected an upstream PGD or APGD oracle")
        if not bool((oracle.mean == 0).all()) or not bool((oracle.std == 1).all()):
            raise ValueError("The cube adapter requires mean=0 and std=1")
        if oracle.steps <= 0 or oracle.restarts < 0:
            raise ValueError("Attacks require positive steps and nonnegative restarts")
        self.oracle = oracle

    @property
    def logic(self):
        return self.oracle.logic

    def attack(self, N, x, y, constraint):
        if not isinstance(constraint, _RelationalConstraint):
            raise TypeError("Expected a local relational Alsomitra constraint")
        region = constraint.precondition
        region._check_tensor(x)
        if x.ndim != 2 or not x.shape[0]:
            raise ValueError("Attacks require a nonempty batch of shape (batch, 6)")
        if isinstance(self.oracle, APGD) and x.dtype != torch.float32:
            raise ValueError("Upstream APGD requires float32 inputs and model; use PGD for float64")
        oracle = copy(self.oracle)
        for name in ("ndim", "min", "max"):
            if hasattr(oracle, name):
                delattr(oracle, name)
        unit = region.encode(region.project(x)).detach()
        model = _DecodedModel(N, region, x.dtype)
        modes = [(module, module.training) for module in N.modules()]
        try:
            N.eval()
            latent = oracle.attack(model, unit, y, _CubeConstraint(constraint))
            candidate = region.decode(latent.to(dtype=x.dtype)).detach()
            if not bool(region.contains(candidate).all()):
                raise ValueError("Attack returned an infeasible candidate")
            return candidate
        finally:
            for module, mode in modes:
                module.training = mode
