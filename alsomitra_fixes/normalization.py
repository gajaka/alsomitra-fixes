"""Frozen Alsomitra data statistics shared by training and verification.

The physical domain is the declared six-decimal domain. Training statistics
come from the actual seed-42 split and are a separate part of the contract.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import io
import json
import math
from pathlib import Path

import numpy as np
import pandas as pd
import torch


DOMAIN_MIN_DECIMAL = ("0.967568", "-0.607397", "-0.356973", "-0.968479", "0.482421", "-41.681405")
DOMAIN_MAX_DECIMAL = ("3.489893", "-0.043021", "0.049180", "-0.068003", "41.714717", "4.197234")
DOMAIN_MIN = tuple(map(float, DOMAIN_MIN_DECIMAL))
DOMAIN_MAX = tuple(map(float, DOMAIN_MAX_DECIMAL))
FEATURE_ORDER = ("v_x", "v_y", "omega", "theta", "x", "y")


def _properties():
    return {
        "P1": {"band": ["-2", "2"], "theta": ["-0.786", "-0.747"],
               "output_bounds": ["0.184", "0.19"]},
        "P2": {"band": ["0", "2"], "v_y_upper": "-0.3", "omega_upper": "-0.12",
               "output_upper": "0.187"},
    }


@dataclass(frozen=True)
class NormalizationContract:
    input_min: tuple[float, ...]
    input_max: tuple[float, ...]
    input_scale: tuple[float, ...]
    output_min: float
    output_max: float
    output_scale: float
    domain_min: tuple[float, ...]
    domain_max: tuple[float, ...]
    train_indices: tuple[int, ...]
    test_indices: tuple[int, ...]
    dataset_sha256: str

    def __post_init__(self):
        for name in ("input_min", "input_max", "input_scale", "domain_min", "domain_max"):
            values = tuple(float(value) for value in getattr(self, name))
            if len(values) != 6 or not all(math.isfinite(value) for value in values):
                raise ValueError(f"{name} must contain six finite numbers")
            object.__setattr__(self, name, values)
        for name in ("output_min", "output_max", "output_scale"):
            value = float(getattr(self, name))
            if not math.isfinite(value):
                raise ValueError(f"{name} must be finite")
            object.__setattr__(self, name, value)
        if self.domain_min != DOMAIN_MIN or self.domain_max != DOMAIN_MAX:
            raise ValueError("The declared physical domain cannot be changed by a normalizer")
        if any(scale <= 0 or scale != maximum - minimum for minimum, maximum, scale
               in zip(self.input_min, self.input_max, self.input_scale)):
            raise ValueError("Input scales must equal positive training max-minus-min values")
        if self.output_scale <= 0 or self.output_scale != self.output_max - self.output_min:
            raise ValueError("Output scale must equal the positive training max-minus-min value")
        for name in ("train_indices", "test_indices"):
            values = tuple(getattr(self, name))
            if any(not isinstance(value, (int, np.integer)) or isinstance(value, bool) for value in values):
                raise ValueError("Dataset indices must be integers")
            object.__setattr__(self, name, tuple(map(int, values)))
        permutation = np.random.RandomState(42).permutation(680)
        if self.train_indices != tuple(map(int, permutation[:544])) or self.test_indices != tuple(map(int, permutation[544:])):
            raise ValueError("The split must be the fixed seed-42 80/20 split of 680 rows")
        if len(self.dataset_sha256) != 64 or any(c not in "0123456789abcdef" for c in self.dataset_sha256):
            raise ValueError("dataset_sha256 must be a lowercase SHA-256 digest")

    def to_dict(self):
        return {
            "schema_version": 1,
            "input_min": list(self.input_min), "input_max": list(self.input_max),
            "input_scale": list(self.input_scale),
            "output_min": self.output_min, "output_max": self.output_max,
            "output_scale": self.output_scale,
            "domain_min": list(self.domain_min), "domain_max": list(self.domain_max),
            "domain_min_decimal": list(DOMAIN_MIN_DECIMAL),
            "domain_max_decimal": list(DOMAIN_MAX_DECIMAL),
            "domain_min_exact_decimal": list(DOMAIN_MIN_DECIMAL),
            "domain_max_exact_decimal": list(DOMAIN_MAX_DECIMAL),
            "train_indices": list(self.train_indices), "test_indices": list(self.test_indices),
            "dataset_sha256": self.dataset_sha256,
            "split_seed": 42, "train_fraction": 0.8, "dataset_shape": [680, 8],
            "feature_order": list(FEATURE_ORDER), "properties": _properties(),
            "input_formula": "normalized=(physical-input_min)/input_scale",
            "output_formula": "physical=output_min+output_scale*normalized",
            "stored_statistics_semantics": "Binary64 constants, preserved by JSON round-trip",
            "binary64_hex": {
                "input_min": [value.hex() for value in self.input_min],
                "input_max": [value.hex() for value in self.input_max],
                "input_scale": [value.hex() for value in self.input_scale],
                "output_min": self.output_min.hex(), "output_max": self.output_max.hex(),
                "output_scale": self.output_scale.hex(),
            },
        }

    @classmethod
    def from_dict(cls, payload):
        if not isinstance(payload, dict) or payload.get("schema_version") != 1:
            raise ValueError("Unsupported Alsomitra normalization contract")
        names = tuple(cls.__dataclass_fields__)
        if not set(names) <= set(payload):
            raise ValueError("Normalization contract fields are missing")
        contract = cls(**{name: payload[name] for name in names})
        if payload != contract.to_dict():
            raise ValueError("Contract metadata, numeric encodings, or property definitions differ from the frozen protocol")
        return contract

    @property
    def digest(self):
        encoded = json.dumps(self.to_dict(), sort_keys=True, separators=(",", ":"), allow_nan=False).encode()
        return hashlib.sha256(encoded).hexdigest()


def as_contract(normalization):
    if isinstance(normalization, NormalizationContract):
        return normalization
    return NormalizationContract.from_dict(normalization)


class NormalizedAlsomitraDataset(torch.utils.data.Dataset):
    """Match the upstream pandas normalization and per-item float32 tensors."""

    def __init__(self, data_all, indices, contract):
        data = data_all.iloc[list(indices)].reset_index(drop=True).copy()
        centre = pd.Series(contract.input_min, index=data.columns[:-2])
        scale = pd.Series(contract.input_scale, index=data.columns[:-2])
        data.iloc[:, :-2] = (data.iloc[:, :-2] - centre) / scale
        data.iloc[:, -1] = (data.iloc[:, -1] - contract.output_min) / contract.output_scale
        # Pandas 3 can expose read-only views; own writable storage keeps
        # torch.from_numpy well-defined while preserving all float32 bytes.
        self.X = np.array(data.iloc[:, :-2].to_numpy(dtype=np.float32, copy=False), copy=True, order="C")
        self.y = np.array(data.iloc[:, -1].to_numpy(dtype=np.float32, copy=False), copy=True, order="C")
        self.indices = tuple(indices)
        self.contract_digest = contract.digest

    def __len__(self):
        return len(self.X)

    def __getitem__(self, index):
        return torch.from_numpy(self.X[index]), torch.tensor([self.y[index]], dtype=torch.float32)


def load_data(csv_path):
    """Read the fixed dataset and split without constructing a model or using global RNG."""
    csv_path = Path(csv_path)
    payload = csv_path.read_bytes()
    data = pd.read_csv(io.BytesIO(payload), header=None)
    if data.shape != (680, 8) or not np.isfinite(data.to_numpy()).all():
        raise ValueError("Expected the finite 680-row, eight-column Alsomitra dataset")
    permutation = np.random.RandomState(42).permutation(len(data))
    train_indices, test_indices = permutation[:544], permutation[544:]
    training = data.iloc[train_indices]
    minimum = training.iloc[:, :-2].min(axis=0).to_numpy(dtype=np.float64)
    maximum = training.iloc[:, :-2].max(axis=0).to_numpy(dtype=np.float64)
    scale = maximum - minimum
    output_min, output_max = float(training.iloc[:, -1].min()), float(training.iloc[:, -1].max())
    if output_min != 0.181 or output_max != 0.193:
        raise ValueError("Training output extrema differ from the frozen protocol's 0.181 and 0.193")
    contract = NormalizationContract(
        tuple(minimum), tuple(maximum), tuple(scale), output_min, output_max, output_max - output_min,
        DOMAIN_MIN, DOMAIN_MAX, tuple(train_indices), tuple(test_indices), hashlib.sha256(payload).hexdigest(),
    )
    return (
        contract,
        NormalizedAlsomitraDataset(data, train_indices, contract),
        NormalizedAlsomitraDataset(data, test_indices, contract),
    )
