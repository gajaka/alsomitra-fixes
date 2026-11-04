"""Frozen data-contract checks for the optional global-region variants.

Synthetic finite CSVs test normalization mechanics, not any empirical claim
about the authors' dataset or training. No model is trained in this module.
"""
from copy import deepcopy
from dataclasses import replace
import hashlib
import json

import numpy as np
import pandas as pd
import pytest
import torch

from alsomitra_fixes.alsomitra_fix import FixedAlsomitraProperty1Constraint, FixedAlsomitraProperty2Constraint
from alsomitra_fixes.normalization import DOMAIN_MIN, DOMAIN_MAX, NormalizationContract, as_contract, load_data


@pytest.fixture
def synthetic_csv(tmp_path):
    rng = np.random.default_rng(418)
    minimum, maximum = np.array(DOMAIN_MIN), np.array(DOMAIN_MAX)
    features = minimum + rng.uniform(0.1, 0.9, size=(680, 6)) * (maximum - minimum)
    output = np.where(np.arange(680) % 2, 0.193, 0.181)
    frame = pd.DataFrame(np.column_stack((features, np.arange(680), output)))
    csv_path = tmp_path / "synthetic_alsomitra.csv"
    frame.to_csv(csv_path, index=False, header=False)
    return csv_path


def test_variant_frozen_split_statistics_and_dataset_float32_bytes(synthetic_csv):
    contract, train, test = load_data(synthetic_csv)
    frame = pd.read_csv(synthetic_csv, header=None)
    permutation = np.random.RandomState(42).permutation(680)
    training = frame.iloc[permutation[:544]]
    minimum = training.iloc[:, :6].min(axis=0)
    scale = training.iloc[:, :6].max(axis=0) - minimum
    assert len(train) == 544 and len(test) == 136
    assert train.indices == tuple(permutation[:544])
    assert test.indices == tuple(permutation[544:])
    assert set(train.indices).isdisjoint(test.indices)
    assert set(train.indices) | set(test.indices) == set(range(680))
    assert contract.dataset_sha256 == hashlib.sha256(synthetic_csv.read_bytes()).hexdigest()
    assert contract.input_min == tuple(minimum)
    assert contract.input_scale == tuple(scale)
    # Physical domain and statistics fitted to the training partition are
    # deliberately different concepts and values.
    assert contract.input_min != contract.domain_min
    assert contract.output_min == 0.181 and contract.output_max == 0.193
    for dataset in (train, test):
        selected = frame.iloc[list(dataset.indices)]
        expected_x = ((selected.iloc[:, :6] - minimum) / scale).to_numpy(dtype=np.float32)
        expected_y = ((selected.iloc[:, -1] - 0.181) / (0.193 - 0.181)).to_numpy(dtype=np.float32)
        assert dataset.X.tobytes() == expected_x.tobytes()
        assert dataset.y.tobytes() == expected_y.tobytes()
        assert dataset.contract_digest == contract.digest
        x, y = dataset[0]
        assert x.dtype == torch.float32 and x.shape == (6,)
        assert y.dtype == torch.float32 and y.shape == (1,)
        assert torch.equal(x, torch.from_numpy(expected_x[0]))
        assert y.item() == expected_y[0]


def test_variant_loading_is_repeatable_and_does_not_consume_global_rng(synthetic_csv):
    before_numpy = np.random.get_state()
    before_torch = torch.get_rng_state().clone()
    first = load_data(synthetic_csv)
    second = load_data(synthetic_csv)
    after_numpy = np.random.get_state()
    assert before_numpy[0] == after_numpy[0]
    assert np.array_equal(before_numpy[1], after_numpy[1])
    assert before_numpy[2:] == after_numpy[2:]
    assert torch.equal(before_torch, torch.get_rng_state())
    assert first[0] == second[0]
    for left, right in zip(first[1:], second[1:]):
        assert left.X.tobytes() == right.X.tobytes()
        assert left.y.tobytes() == right.y.tobytes()


def test_variant_contract_json_roundtrip_preserves_binary64_and_digest(synthetic_csv):
    contract, _, _ = load_data(synthetic_csv)
    payload = json.loads(json.dumps(contract.to_dict(), allow_nan=False))
    reconstructed = NormalizationContract.from_dict(payload)
    assert reconstructed == contract
    assert reconstructed.to_dict() == contract.to_dict()
    assert reconstructed.digest == contract.digest
    assert len(contract.digest) == 64
    assert as_contract(contract) is contract
    assert as_contract(payload) == contract


@pytest.mark.parametrize("field", ["split_seed", "properties", "binary64_hex", "dataset_sha256", "extra", "missing"])
def test_variant_contract_metadata_tampering_is_rejected(synthetic_csv, field):
    contract, _, _ = load_data(synthetic_csv)
    payload = deepcopy(contract.to_dict())
    if field == "split_seed":
        payload[field] = 43
    elif field == "properties":
        payload[field]["P2"]["output_upper"] = "0.188"
    elif field == "binary64_hex":
        payload[field]["output_scale"] = float(1).hex()
    elif field == "dataset_sha256":
        payload[field] = "not a digest"
    elif field == "extra":
        payload["extra"] = "unrecognized metadata"
    else:
        del payload["input_scale"]
    with pytest.raises(ValueError):
        NormalizationContract.from_dict(payload)


def test_variant_contract_rejects_changed_domain_split_and_degenerate_scale(synthetic_csv):
    contract, _, _ = load_data(synthetic_csv)
    for changes in (
        {"input_scale": (0.0, *contract.input_scale[1:])},
        {"domain_min": (0.0, *contract.domain_min[1:])},
        {"train_indices": tuple(reversed(contract.train_indices))},
        {"output_scale": float("nan")},
    ):
        with pytest.raises(ValueError):
            replace(contract, **changes)


@pytest.mark.parametrize("corruption", ["shape", "nonfinite", "constant_input", "wrong_output_extrema"])
def test_variant_invalid_dataset_fails_before_model_construction(synthetic_csv, corruption):
    frame = pd.read_csv(synthetic_csv, header=None)
    if corruption == "shape":
        frame = frame.iloc[:-1]
    elif corruption == "nonfinite":
        frame.iloc[0, 0] = float("inf")
    elif corruption == "constant_input":
        frame.iloc[:, 0] = 2.0
    else:
        frame.iloc[:, -1] = np.where(np.arange(680) % 2, 0.194, 0.182)
    frame.to_csv(synthetic_csv, index=False, header=False)
    with pytest.raises(ValueError):
        load_data(synthetic_csv)


@pytest.mark.parametrize("factory", [FixedAlsomitraProperty1Constraint, FixedAlsomitraProperty2Constraint])
@pytest.mark.parametrize("dtype", [torch.float32, torch.float64])
def test_variant_shared_data_normalization_preserves_physical_region_and_output_thresholds(synthetic_csv, factory, dtype):
    contract, _, _ = load_data(synthetic_csv)
    constraint = factory(torch.device("cpu"), normalization=contract.to_dict())
    region = constraint.precondition
    unit = torch.cat((torch.zeros(1, 6), torch.ones(1, 6), torch.full((1, 6), 0.5))).to(dtype=dtype)
    candidate = region.decode(unit)
    # Independently undo the *data* normalizer, not the physical-domain
    # normalizer. In this optional mode physical endpoints can normalize
    # outside [0,1]; the latent attack cube remains [0,1].
    physical = candidate.to(torch.float64) * torch.tensor(contract.input_scale, dtype=torch.float64) + torch.tensor(contract.input_min, dtype=torch.float64)
    tolerance = 3e-5 if dtype == torch.float32 else 1e-12
    assert (physical >= torch.tensor(DOMAIN_MIN, dtype=torch.float64) - tolerance).all()
    assert (physical <= torch.tensor(DOMAIN_MAX, dtype=torch.float64) + tolerance).all()
    actual_band = physical[:, 4] + physical[:, 5]
    if factory is FixedAlsomitraProperty1Constraint:
        assert (actual_band >= -2 - tolerance).all()
        assert (actual_band <= 2 + tolerance).all()
        assert (physical[:, 3] >= -0.786 - tolerance).all()
        assert (physical[:, 3] <= -0.747 + tolerance).all()
        assert constraint.postcondition.lo.item() == pytest.approx((0.184 - contract.output_min) / contract.output_scale)
        upper = 0.19
    else:
        assert (actual_band >= -tolerance).all()
        assert (actual_band <= 2 + tolerance).all()
        assert (physical[:, 1] <= -0.3 + tolerance).all()
        assert (physical[:, 2] <= -0.12 + tolerance).all()
        assert np.isnan(constraint.postcondition.lo.item())
        upper = 0.187
    assert constraint.postcondition.hi.item() == pytest.approx((upper - contract.output_min) / contract.output_scale)
    assert ((candidate < 0) | (candidate > 1)).any()
    assert region.contains(candidate).all()
    torch.testing.assert_close(region.decode(region.encode(candidate)), candidate, atol=2e-6 if dtype == torch.float32 else 1e-13, rtol=0)
