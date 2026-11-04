"""Regression checks for the audit runner; no Lean or Lake process is started.

The mocked process outputs exercise failure handling, complete root coverage
and axiom policy. They are not substitutes for the separate actual Lean audit.
"""
from __future__ import annotations

import csv
import importlib.util
from pathlib import Path
from types import SimpleNamespace

import pytest


SOURCE = Path(__file__).resolve().parents[1] / "lean" / "run_lean_audit.py"


@pytest.fixture
def runner():
    spec = importlib.util.spec_from_file_location("alsomitra_lean_audit_under_test", SOURCE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lines(runner):
    return "".join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                   for name in runner.EXPECTED_THEOREMS)


def run_case(runner, tmp_path, monkeypatch, *, audit_output=None, audit_code=0,
             audit_stderr="", version_code=0, version_output="Lean test version",
             build_code=0, build_output="Build completed successfully.\n",
             source="", requests=None):
    project = tmp_path / "lean"
    project.mkdir()
    (project / "AlsomitraFixes").mkdir()
    (project / "AlsomitraFixes.lean").write_text(source)
    wanted = runner.EXPECTED_THEOREMS if requests is None else requests
    (project / "Audit.lean").write_text("\n".join("#print axioms " + name for name in wanted) + "\n")
    monkeypatch.setattr(runner, "ROOT", project)
    monkeypatch.setattr(runner, "RESULTS", project / "results")
    calls = []

    def mocked_run(command):
        calls.append(command)
        if command == ["lake", "env", "lean", "--version"]:
            return SimpleNamespace(returncode=version_code, stdout=version_output, stderr="")
        if command == ["lake", "build"]:
            return SimpleNamespace(returncode=build_code, stdout=build_output, stderr="")
        assert command == ["lake", "env", "lean", "Audit.lean"]
        return SimpleNamespace(returncode=audit_code,
                               stdout=lines(runner) if audit_output is None else audit_output,
                               stderr=audit_stderr)

    monkeypatch.setattr(runner, "run", mocked_run)
    with pytest.raises(SystemExit) as stopped:
        runner.main()
    with (project / "results/lean_run_info.csv").open() as stream:
        info = {row["key"]: row["value"] for row in csv.DictReader(stream)}
    with (project / "results/lean_theorems.csv").open() as stream:
        rows = list(csv.DictReader(stream))
    return stopped.value.code, info, rows, calls


def test_complete_standard_axiom_audit_succeeds(runner, tmp_path, monkeypatch):
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch)
    assert code == 0
    assert info["audit_exit_code"] == "0" and info["audit_coverage_complete"] == "True"
    assert len(rows) == len(runner.EXPECTED_THEOREMS) == 12


def test_failed_audit_after_valid_row_is_rejected(runner, tmp_path, monkeypatch):
    output = lines(runner).splitlines(keepends=True)[0]
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch, audit_output=output, audit_code=1,
        audit_stderr="Audit.lean:9:0: error: unknown constant 'missing_root'\n")
    assert code == 1 and len(rows) == 1
    assert info["audit_ok"] == "False" and info["audit_errors"] == "1"


def test_failed_audit_with_complete_clean_output_is_rejected(runner, tmp_path, monkeypatch):
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch, audit_code=1)
    assert code == 1 and len(rows) == 12
    assert info["audit_coverage_complete"] == "True"
    assert info["audit_errors"] == "0" and info["audit_warnings"] == "0"
    assert info["audit_ok"] == "False"


def test_successful_but_partial_audit_is_rejected(runner, tmp_path, monkeypatch):
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch,
                                  audit_output=lines(runner).splitlines(keepends=True)[0])
    assert code == 1 and len(rows) == 1
    assert info["audit_ok"] == "True" and info["audit_coverage_complete"] == "False"
    assert len(info["missing_theorems"].split()) == 11


def test_duplicate_root_is_rejected(runner, tmp_path, monkeypatch):
    output = lines(runner) + lines(runner).splitlines(keepends=True)[0]
    code, info, _, _ = run_case(runner, tmp_path, monkeypatch, audit_output=output)
    assert code == 1 and info["duplicate_theorems"] == runner.EXPECTED_THEOREMS[0]


def test_wrong_root_cannot_replace_expected_root(runner, tmp_path, monkeypatch):
    output = lines(runner).replace(runner.EXPECTED_THEOREMS[0], "Other.unexpected")
    code, info, _, _ = run_case(runner, tmp_path, monkeypatch, audit_output=output)
    assert code == 1 and info["missing_theorems"] == runner.EXPECTED_THEOREMS[0]
    assert info["unexpected_theorems"] == "Other.unexpected"


@pytest.mark.parametrize("axiom", ["foreignAxiom", "sorryAx"])
def test_nonstandard_axioms_are_rejected(runner, tmp_path, monkeypatch, axiom):
    output = lines(runner).replace("propext, Classical.choice, Quot.sound", axiom, 1)
    code, info, _, _ = run_case(runner, tmp_path, monkeypatch, audit_output=output)
    assert code == 1 and info["theorems_with_nonstandard_axioms"] == "1"


def test_axiom_free_output_is_counted(runner, tmp_path, monkeypatch):
    name = runner.EXPECTED_THEOREMS[0]
    output = lines(runner).replace(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]",
                                   f"'{name}' does not depend on any axioms")
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch, audit_output=output)
    assert code == 0 and info["audit_coverage_complete"] == "True"
    assert rows[0]["axioms"] == "" and rows[0]["only_standard_axioms"] == "True"


@pytest.mark.parametrize("message", ["warning: diagnostic\n", "Audit.lean:8:0: warning: diagnostic\n"])
def test_audit_warning_is_rejected(runner, tmp_path, monkeypatch, message):
    code, info, _, _ = run_case(runner, tmp_path, monkeypatch, audit_stderr=message)
    assert code == 1 and info["audit_warnings"] == "1"


def test_zero_exit_audit_error_is_rejected(runner, tmp_path, monkeypatch):
    code, info, _, _ = run_case(runner, tmp_path, monkeypatch,
                               audit_stderr="Audit.lean:8:0: error: diagnostic\n")
    assert code == 1 and info["audit_errors"] == "1"


def test_empty_audit_is_rejected(runner, tmp_path, monkeypatch):
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch, audit_output="")
    assert code == 1 and not rows and info["audit_coverage_complete"] == "False"


def test_empty_expected_root_set_is_rejected(runner, tmp_path, monkeypatch):
    monkeypatch.setattr(runner, "EXPECTED_THEOREMS", ())
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch, audit_output="")
    assert code == 1 and not rows
    assert info["theorems_expected"] == "0" and info["audit_coverage_complete"] == "False"


def test_failed_build_does_not_run_audit(runner, tmp_path, monkeypatch):
    code, info, rows, calls = run_case(runner, tmp_path, monkeypatch, build_code=1)
    assert code == 1 and not rows and info["build_ok"] == "False"
    assert ["lake", "env", "lean", "Audit.lean"] not in calls


@pytest.mark.parametrize("diagnostic", ["warning", "error"])
def test_build_diagnostic_is_rejected(runner, tmp_path, monkeypatch, diagnostic):
    code, info, rows, _ = run_case(runner, tmp_path, monkeypatch,
                                  build_output=f"Project.lean:1:0: {diagnostic}: diagnostic\n")
    assert code == 1 and not rows and info["build_" + diagnostic + "s"] == "1"


@pytest.mark.parametrize("code,output", [(1, "Lean version unavailable"), (0, "")])
def test_invalid_version_command_stops_build(runner, tmp_path, monkeypatch, code, output):
    exit_code, info, _, calls = run_case(runner, tmp_path, monkeypatch,
                                       version_code=code, version_output=output)
    assert exit_code == 1 and info["version_ok"] == "False"
    assert ["lake", "build"] not in calls


def test_changed_audit_request_list_is_rejected(runner, tmp_path, monkeypatch):
    code, info, _, calls = run_case(runner, tmp_path, monkeypatch, requests=runner.EXPECTED_THEOREMS[:1])
    assert code == 1 and info["audit_requests_match_expected"] == "False"
    assert ["lake", "env", "lean", "Audit.lean"] not in calls


def test_comments_and_strings_do_not_count_as_proof_placeholders(runner, tmp_path, monkeypatch):
    source = '-- no sorry here\n/- nested /- admit -/ comment -/\ndef message := "sorry and admit"\n'
    code, info, _, _ = run_case(runner, tmp_path, monkeypatch, source=source)
    assert code == 0 and info["files_with_sorry"] == "none"


@pytest.mark.parametrize("placeholder", ["sorry", "admit"])
def test_actual_proof_placeholder_is_rejected(runner, tmp_path, monkeypatch, placeholder):
    code, info, _, calls = run_case(runner, tmp_path, monkeypatch,
                                   source=f"theorem unfinished : True := by {placeholder}\n")
    assert code == 1 and info["files_with_sorry"] == "AlsomitraFixes.lean"
    assert ["lake", "env", "lean", "Audit.lean"] not in calls


def test_declared_short_audit_names_match_current_package(runner):
    assert runner.declared_theorems(SOURCE.parent / "Audit.lean") == runner.EXPECTED_THEOREMS


def test_colored_positioned_diagnostics_are_detected(runner):
    assert runner.diagnostics("\x1b[33mAudit.lean:4:0: warning: first\x1b[0m\nerror: second\n") == (1, 1)
