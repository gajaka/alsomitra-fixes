"""The two implementation corrections, preserving upstream anchor rectangles.

Unlike the optional coupled regions in ``alsomitra_fix``, these classes retain
the framework paper's input region relative to the original anchor. They do
not change sampling, attack behavior, Property1's theta bound, or output scale.
The equivalent two-file upstream diff is ``upstream_property2.patch``.

Derived from property-driven-ml at 616df1e; see LICENSE.upstream.
"""
import numpy as np
import torch

from property_driven_ml.constraints.constraints import Constraint
from property_driven_ml.constraints.postconditions import AlsomitraOutputPostcondition
from property_driven_ml.constraints.preconditions import AlsomitraProperty2


class CorrectedAlsomitraProperty2(AlsomitraProperty2):
    """Compute physical bounds and let apply_domain_bounds normalize once."""

    def get_bounds(self, x):
        physical_anchor = self.denormalize(x)
        lo = torch.full_like(physical_anchor, torch.nan)
        hi = torch.full_like(physical_anchor, torch.nan)
        lo[:, self.y] = -physical_anchor[:, self.x]
        hi[:, self.y] = self.y_threshold - physical_anchor[:, self.x]
        hi[:, self.v_y] = self.v_y_threshold
        hi[:, self.omega] = self.omega_threshold
        # FIX: apply_domain_bounds expects physical values and normalizes them.
        return self.apply_domain_bounds(lo, hi)


class CorrectedAlsomitraProperty2Constraint(Constraint):
    """Preserve the framework's local rectangle and correct argument binding."""

    def __init__(self, device, y_threshold=2.0, v_y_threshold=-0.3,
                 omega_threshold=-0.12, bounds_output=(np.nan, 0.187)):
        super().__init__(device)
        # FIX: keyword arguments bind each threshold to its actual quantity.
        self.precondition = CorrectedAlsomitraProperty2(
            device, v_y_threshold=v_y_threshold, y_threshold=y_threshold,
            omega_threshold=omega_threshold,
        )
        self.postcondition = AlsomitraOutputPostcondition(
            device, lo=bounds_output[0], hi=bounds_output[1],
        )
