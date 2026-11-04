"""Regression controls for checkout provenance and fresh pytest reporting.

Git answers are controlled locally; import-location checks use real small
Python packages in temporary directories. No upstream files are modified.
"""
from __future__ import annotations

import csv
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
from types import SimpleNamespace

import pytest


@pytest.fixture
def runner(tmp_path, monkeypatch):
    source = Path(__file__).resolve().parents[1] / "run_python_tests.py"
    spec = importlib.util.spec_from_file_location("alsomitra_python_runner_under_test", source)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    project = tmp_path / "project"
    project.mkdir()
    monkeypatch.setattr(module, "ROOT", project)
    monkeypatch.setattr(module, "RESULTS", project / "results")
    return module


@pytest.fixture
def checkout(runner, tmp_path, monkeypatch):
    root = tmp_path / "upstream"
    package = root / "src" / "property_driven_ml"
    for relative in runner.SOURCE_MODULES.values():
        source = package / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("# Isolated provenance fixture.\n")
    for subpackage in ("constraints", "training"):
        (package / subpackage / "__init__.py").write_text("")
    tracked = [str(p.relative_to(root)) for p in package.rglob("*.py")]
    answers = {
        ("rev-parse", "--show-toplevel"): str(root),
        ("rev-parse", "HEAD"): runner.EXPECTED_REVISION,
        ("status", "--porcelain", "--untracked-files=no"): "",
        ("ls-files", "--", "src/property_driven_ml"): "\n".join(tracked),
    }
    monkeypatch.setattr(runner, "git_output", lambda path, *args: answers[args])
    return root, package, answers


def test_clean_pinned_checkout_and_real_import_locations(runner, checkout):
    root, package, _ = checkout
    report = runner.inspect_upstream(root)
    assert report["ok"] and report["tracked_clean"] and report["imports_match"]
    assert report["revision"] == runner.EXPECTED_REVISION
    assert set(report["imports"]) == set(runner.SOURCE_MODULES)
    for name, item in report["imports"].items():
        assert item["path"] == str((package / runner.SOURCE_MODULES[name]).resolve())
        assert len(item["sha256"]) == 64


def test_real_project_package_shadow_is_rejected(runner, checkout):
    root, package, _ = checkout
    shutil.copytree(package, runner.ROOT / "property_driven_ml")
    report = runner.inspect_upstream(root)
    assert not report["ok"] and not report["imports_match"]
    assert "outside the requested package" in report["error"]


def test_real_git_tree_checks_tracked_and_ignored_added_sources(runner, tmp_path, monkeypatch):
    """Exercise real Git status/index behavior rather than simulated answers."""
    root = tmp_path / "real-checkout"
    package = root / "src" / "property_driven_ml"
    for relative in runner.SOURCE_MODULES.values():
        path = package / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("# Original tracked module.\n")
    for subpackage in ("constraints", "training"):
        (package / subpackage / "__init__.py").write_text("")

    def git(*args):
        completed = subprocess.run(["git", "-C", str(root), *args],
                                   capture_output=True, text=True, check=True)
        return completed.stdout.strip()

    git("init", "-q")
    git("add", "src")
    git("-c", "user.name=Test Fixture", "-c", "user.email=fixture@example.invalid",
        "-c", "commit.gpgsign=false", "commit", "-qm", "Isolated fixture")
    monkeypatch.setattr(runner, "EXPECTED_REVISION", git("rev-parse", "HEAD"))
    assert runner.inspect_upstream(root)["ok"]

    source = package / "constraints/preconditions.py"
    original = source.read_text()
    source.write_text(original + "changed = True\n")
    dirty = runner.inspect_upstream(root)
    assert not dirty["ok"] and not dirty["tracked_clean"]
    assert "modified tracked files" in dirty["error"]

    source.write_text(original)
    (root / ".git/info/exclude").write_text("hidden_added.py\n")
    (package / "hidden_added.py").write_text("# Git ignores this source addition.\n")
    assert git("status", "--porcelain") == ""
    added = runner.inspect_upstream(root)
    assert not added["ok"] and added["tracked_clean"]
    assert "added Python package sources" in added["error"]


def test_wrong_revision_is_rejected_before_import(runner, checkout, monkeypatch):
    root, _, answers = checkout
    answers[("rev-parse", "HEAD")] = "0" * 40
    monkeypatch.setattr(runner.subprocess, "run", lambda *a, **k: pytest.fail("Must not import a wrong revision"))
    report = runner.inspect_upstream(root)
    assert not report["ok"] and "pinned revision" in report["error"]


def test_dirty_checkout_at_expected_head_is_rejected_before_import(runner, checkout, monkeypatch):
    root, _, answers = checkout
    answers[("status", "--porcelain", "--untracked-files=no")] = " M src/property_driven_ml/constraints/constraints.py"
    monkeypatch.setattr(runner.subprocess, "run", lambda *a, **k: pytest.fail("Must not import modified tracked source"))
    report = runner.inspect_upstream(root)
    assert report["revision"] == runner.EXPECTED_REVISION
    assert not report["ok"] and not report["tracked_clean"]
    assert "modified tracked files" in report["error"]


def test_upstream_argument_must_be_actual_checkout_root(runner, checkout):
    root, _, answers = checkout
    answers[("rev-parse", "--show-toplevel")] = str(root.parent)
    report = runner.inspect_upstream(root)
    assert not report["ok"] and "checkout root" in report["error"]


def test_source_directory_must_exist(runner, tmp_path):
    report = runner.inspect_upstream(tmp_path / "missing")
    assert not report["ok"] and "src/property_driven_ml" in report["error"]


@pytest.mark.parametrize("suffix", [".py", ".pyi"])
def test_added_package_source_is_rejected_even_when_git_ignores_it(runner, checkout, suffix):
    root, package, _ = checkout
    (package / ("untracked_extra" + suffix)).write_text("# Not part of the pinned tree.\n")
    report = runner.inspect_upstream(root)
    assert report["tracked_clean"]
    assert not report["ok"] and "added Python package sources" in report["error"]
    assert report["untracked_package_sources"] == ["src/property_driven_ml/untracked_extra" + suffix]


def test_required_module_must_be_present_and_tracked(runner, checkout):
    root, package, _ = checkout
    (package / "constraints/preconditions.py").unlink()
    report = runner.inspect_upstream(root)
    assert not report["ok"] and "absent or untracked" in report["error"]


@pytest.mark.parametrize("outside", [True, False])
def test_unexpected_import_origin_is_rejected(runner, checkout, monkeypatch, outside):
    root, package, _ = checkout
    origins = {name: str(package / relative) for name, relative in runner.SOURCE_MODULES.items()}
    module = "property_driven_ml.constraints.preconditions"
    origins[module] = str(root / "installed_elsewhere.py") if outside else str(package / "__init__.py")
    completed = SimpleNamespace(returncode=0, stdout="ALSOMITRA_IMPORTS " + json.dumps(origins) + "\n", stderr="")
    monkeypatch.setattr(runner.subprocess, "run", lambda *a, **k: completed)
    report = runner.inspect_upstream(root)
    assert not report["ok"] and not report["imports_match"]
    assert ("outside" if outside else "Unexpected") in report["error"]


def test_import_probe_failure_is_not_silently_accepted(runner, checkout, monkeypatch):
    root, _, _ = checkout
    monkeypatch.setattr(runner.subprocess, "run", lambda *a, **k:
                        SimpleNamespace(returncode=1, stdout="", stderr="ModuleNotFoundError"))
    report = runner.inspect_upstream(root)
    assert not report["ok"] and "import probe failed" in report["error"]


def test_git_command_failure_is_not_silently_accepted(runner, tmp_path, monkeypatch):
    monkeypatch.setattr(runner.subprocess, "run", lambda *a, **k:
                        SimpleNamespace(returncode=128, stdout="", stderr="not a repository"))
    with pytest.raises(ValueError, match="not a repository"):
        runner.upstream_revision(tmp_path)


def test_probe_and_tests_replace_ambient_pythonpath(runner, tmp_path, monkeypatch):
    monkeypatch.setenv("PYTHONPATH", "/unexpected/installed/package")
    env = runner.test_environment(tmp_path)
    assert env["PYTHONPATH"].split(runner.os.pathsep) == [str(runner.ROOT), str(tmp_path / "src"), str(tmp_path)]
    assert "/unexpected/installed/package" not in env["PYTHONPATH"]


def _report(runner, **changes):
    report = {"ok": True, "revision": runner.EXPECTED_REVISION, "git_root": "/fixture/upstream",
              "tracked_clean": True, "untracked_package_sources": [], "imports_match": True,
              "imports": {"module": {"path": "/fixture/upstream/source.py", "sha256": "a" * 64}}, "error": ""}
    return {**report, **changes}


def _run_main(runner, monkeypatch, reports, test_result):
    sequence = iter(reports)
    monkeypatch.setattr(runner, "inspect_upstream", lambda path: next(sequence))
    monkeypatch.setattr(runner, "package_version", lambda name: "test-version")
    monkeypatch.setattr(runner, "run_tests", test_result)
    monkeypatch.setattr(sys, "argv", ["run_python_tests.py", "--upstream", str(runner.ROOT / "upstream")])
    with pytest.raises(SystemExit) as result:
        runner.main()
    with (runner.RESULTS / "python_run_info.csv").open() as stream:
        info = {row["key"]: row["value"] for row in csv.DictReader(stream)}
    return result.value.code, info


def _passed_row():
    return {"test_file": "tests/example.py", "test_name": "example", "outcome": "passed", "seconds": "0.001", "message": ""}


def test_main_does_not_run_tests_after_failed_preflight(runner, monkeypatch):
    rejected = _report(runner, ok=False, tracked_clean=False, error="modified tracked files")
    code, info = _run_main(runner, monkeypatch, [rejected],
                           lambda path: pytest.fail("Tests must not run after failed provenance"))
    assert code == 1
    assert info["pytest_exit_code"] == "not run"
    assert info["upstream_preflight_ok"] == "False"
    assert info["tests_passed"] == "0/0"


def test_main_accepts_only_passing_tests_and_matching_pre_post_provenance(runner, monkeypatch):
    good = _report(runner)
    code, info = _run_main(runner, monkeypatch, [good, good], lambda path: (0, [_passed_row()]))
    assert code == 0 and info["tests_passed"] == "1/1"
    assert info["run_status"] == "PASS" and info["upstream_imports_unchanged"] == "True"
    assert info["upstream_postflight_ok"] == "True"
    assert json.loads(info["upstream_imports_before"]) == good["imports"]


def test_main_rejects_checkout_changed_during_tests(runner, monkeypatch):
    before = _report(runner)
    after = _report(runner, ok=False, tracked_clean=False, error="modified tracked files")
    code, info = _run_main(runner, monkeypatch, [before, after], lambda path: (0, [_passed_row()]))
    assert code == 1 and info["tests_passed"] == "1/1"
    assert info["upstream_postflight_ok"] == "False"
    assert "modified tracked files" in info["upstream_provenance_error"]


def test_main_rejects_import_bytes_changed_even_if_status_claims_clean(runner, monkeypatch):
    before = _report(runner)
    after = _report(runner, imports={"module": {"path": "/fixture/upstream/source.py", "sha256": "b" * 64}})
    code, info = _run_main(runner, monkeypatch, [before, after], lambda path: (0, [_passed_row()]))
    assert code == 1
    assert info["run_status"] == "FAIL" and info["upstream_imports_unchanged"] == "False"
    assert "source files changed" in info["upstream_provenance_error"]


@pytest.mark.parametrize("return_code, rows", [(1, [_passed_row()]), (0, [])])
def test_main_does_not_accept_failed_or_empty_pytest(runner, monkeypatch, return_code, rows):
    good = _report(runner)
    code, _ = _run_main(runner, monkeypatch, [good, good], lambda path: (return_code, rows))
    assert code == 1


def test_stale_junit_is_deleted_before_new_pytest(runner, tmp_path, monkeypatch):
    runner.RESULTS.mkdir()
    old = runner.RESULTS / "pytest-junit.xml"
    old.write_text('<testsuite><testcase classname="old" name="old"/></testsuite>')
    def no_fresh_report(*args, **kwargs):
        assert not old.exists()
        return SimpleNamespace(returncode=0, stdout="", stderr="")
    monkeypatch.setattr(runner.subprocess, "run", no_fresh_report)
    code, rows = runner.run_tests(tmp_path)
    assert code == 0 and rows == [] and not old.exists()


def test_malformed_new_junit_is_rejected(runner, tmp_path, monkeypatch):
    runner.RESULTS.mkdir()
    def malformed(*args, **kwargs):
        (runner.RESULTS / "pytest-junit.xml").write_text("<broken")
        return SimpleNamespace(returncode=0, stdout="", stderr="")
    monkeypatch.setattr(runner.subprocess, "run", malformed)
    code, rows = runner.run_tests(tmp_path)
    assert code == 1 and rows == []


def test_fresh_failure_report_keeps_failed_outcome(runner, tmp_path, monkeypatch):
    runner.RESULTS.mkdir()
    def failed(*args, **kwargs):
        (runner.RESULTS / "pytest-junit.xml").write_text(
            '<testsuite><testcase classname="tests.example" name="failed" time="0.01">'
            '<failure message="real failure"/></testcase></testsuite>')
        return SimpleNamespace(returncode=1, stdout="one failed", stderr="")
    monkeypatch.setattr(runner.subprocess, "run", failed)
    code, rows = runner.run_tests(tmp_path)
    assert code == 1 and len(rows) == 1 and rows[0]["outcome"] == "failed"
    assert rows[0]["message"] == "real failure"
