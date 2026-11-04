"""Run the Python tests and write their results to CSV files.

Usage, from this directory:

    python run_python_tests.py --upstream /path/to/property-driven-ml

`--upstream` is a checkout of property-driven-ml at revision 616df1e. The
script needs torch, numpy, pandas and pytest. It does not run Lean; the Lean
checks have their own script, lean/run_lean_audit.py.

Writes:
    results/python_tests.csv     one row per test
    results/python_run_info.csv  environment, upstream revision, totals

Before and after testing, the runner verifies the checkout root, pinned HEAD,
tracked-file cleanliness, absence of added Python package sources, and actual
import locations. A failed provenance check or a non-passing test exits nonzero.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import platform
import subprocess
import sys
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
EXPECTED_REVISION = "616df1e5baaabf7b42dc26320c00fb297903c87a"
SOURCE_MODULES = {
    "property_driven_ml": "__init__.py",
    "property_driven_ml.constraints.constraints": "constraints/constraints.py",
    "property_driven_ml.constraints.preconditions": "constraints/preconditions.py",
    "property_driven_ml.constraints.postconditions": "constraints/postconditions.py",
    "property_driven_ml.training.attacks": "training/attacks.py",
}


def test_environment(upstream):
    """Use the same explicit package search path for probes and pytest."""
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join((str(ROOT), str(upstream / "src"), str(upstream)))
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONNOUSERSITE"] = "1"
    return env


def git_output(upstream, *args):
    completed = subprocess.run(["git", *args], cwd=upstream, capture_output=True, text=True)
    if completed.returncode:
        raise ValueError(completed.stderr.strip() or "Git checkout inspection failed")
    return completed.stdout.strip()


def upstream_revision(upstream):
    return git_output(upstream, "rev-parse", "HEAD")


def inspect_upstream(upstream):
    """Fail closed before importing a modified or unexpectedly resolved package.

    This is provenance evidence for this run, not a Python execution sandbox.
    Added .py/.pyi files are checked even if Git would ignore them.
    """
    upstream = Path(upstream).resolve()
    report = {"ok": False, "revision": "unknown", "git_root": "unknown",
              "tracked_clean": False, "untracked_package_sources": [],
              "imports_match": False, "imports": {}, "error": ""}
    try:
        package = upstream / "src" / "property_driven_ml"
        if not upstream.is_dir() or not package.is_dir():
            raise ValueError("--upstream must contain src/property_driven_ml")
        report["git_root"] = git_output(upstream, "rev-parse", "--show-toplevel")
        if Path(report["git_root"]).resolve() != upstream:
            raise ValueError("--upstream must be the Git checkout root")
        report["revision"] = upstream_revision(upstream)
        if report["revision"] != EXPECTED_REVISION:
            raise ValueError("Upstream HEAD does not match the pinned revision")
        changes = git_output(upstream, "status", "--porcelain", "--untracked-files=no")
        report["tracked_clean"] = not changes
        if changes:
            raise ValueError("Upstream has modified tracked files: " + changes.replace("\n", "; "))
        tracked = set(git_output(upstream, "ls-files", "--", "src/property_driven_ml").splitlines())
        for relative in SOURCE_MODULES.values():
            name = "src/property_driven_ml/" + relative
            if name not in tracked or not (package / relative).is_file():
                raise ValueError("A required upstream module is absent or untracked: " + name)
        additions = sorted(str(path.relative_to(upstream)) for path in package.rglob("*")
                           if path.is_file() and path.suffix in (".py", ".pyi")
                           and str(path.relative_to(upstream)) not in tracked)
        report["untracked_package_sources"] = additions
        if additions:
            raise ValueError("Upstream contains added Python package sources: " + "; ".join(additions))
        probe = (
            "import importlib,json\n"
            "names=" + repr(list(SOURCE_MODULES)) + "\n"
            "found={name:importlib.import_module(name).__file__ for name in names}\n"
            "print('ALSOMITRA_IMPORTS '+json.dumps(found,sort_keys=True))\n"
        )
        completed = subprocess.run([sys.executable, "-c", probe], cwd=ROOT,
                                   env=test_environment(upstream), capture_output=True, text=True)
        if completed.returncode:
            raise ValueError("Upstream import probe failed: " + completed.stderr.strip())
        markers = [line.removeprefix("ALSOMITRA_IMPORTS ") for line in completed.stdout.splitlines()
                   if line.startswith("ALSOMITRA_IMPORTS ")]
        if len(markers) != 1:
            raise ValueError("Import probe did not return one complete module report")
        origins = json.loads(markers[0])
        if set(origins) != set(SOURCE_MODULES):
            raise ValueError("Import probe returned an incomplete or unexpected module set")
        for module, relative in SOURCE_MODULES.items():
            actual = Path(origins[module]).resolve()
            expected = (package / relative).resolve()
            try:
                actual.relative_to(package.resolve())
            except ValueError as exc:
                raise ValueError("Imported module is outside the requested package: " + module) from exc
            if actual != expected:
                raise ValueError("Unexpected imported module location: " + module)
            report["imports"][module] = {
                "path": str(actual), "sha256": hashlib.sha256(actual.read_bytes()).hexdigest(),
            }
        report["imports_match"] = True
        report["ok"] = True
    except (OSError, ValueError, TypeError, KeyError) as exc:
        report["error"] = str(exc)
    return report


def package_version(name):
    try:
        return getattr(__import__(name), "__version__", "unknown")
    except ImportError:
        return "not installed"


def run_tests(upstream):
    junit = RESULTS / "pytest-junit.xml"
    # A missing/newly failed pytest invocation must not reuse a previous XML.
    junit.unlink(missing_ok=True)
    env = test_environment(upstream)
    command = [sys.executable, "-m", "pytest", "tests", "-q", "-p", "no:cacheprovider",
               f"--junitxml={junit}"]
    completed = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
    print(completed.stdout)
    if completed.stderr:
        print(completed.stderr, file=sys.stderr)
    if not junit.exists():
        return completed.returncode, []
    rows = []
    try:
        cases = list(ET.parse(junit).getroot().iter("testcase"))
    except (ET.ParseError, OSError) as exc:
        print(f"Cannot read the fresh pytest report: {exc}", file=sys.stderr)
        junit.unlink(missing_ok=True)
        return completed.returncode or 1, []
    for case in cases:
        outcome, message = "passed", ""
        for tag, label in (("failure", "failed"), ("error", "error"), ("skipped", "skipped")):
            node = case.find(tag)
            if node is not None:
                outcome = label
                message = (node.get("message") or "").splitlines()[0][:200] if node.get("message") else ""
        rows.append({
            "test_file": case.get("classname", "").replace(".", "/") + ".py",
            "test_name": case.get("name", ""),
            "outcome": outcome,
            "seconds": f"{float(case.get('time', 0)):.4f}",
            "message": message,
        })
    junit.unlink()
    return completed.returncode, rows


def write_csv(path, rows, fields):
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description="Run the Python tests and write CSV results.")
    parser.add_argument("--upstream", required=True, type=Path,
                        help="checkout of property-driven-ml at revision 616df1e")
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    RESULTS.mkdir(exist_ok=True)

    before = inspect_upstream(upstream)
    code, rows, after = None, [], None
    if before["ok"]:
        code, rows = run_tests(upstream)
        after = inspect_upstream(upstream)
    else:
        print("Upstream provenance check failed: " + before["error"], file=sys.stderr)
    write_csv(RESULTS / "python_tests.csv", rows,
              ["test_file", "test_name", "outcome", "seconds", "message"])

    passed = sum(row["outcome"] == "passed" for row in rows)
    imports_unchanged = after is not None and before["imports"] == after["imports"]
    provenance_error = before["error"] or (after["error"] if after else "")
    if before["ok"] and after is not None and after["ok"] and not imports_unchanged:
        provenance_error = "Imported source files changed during testing"
    ok = (before["ok"] and after is not None and after["ok"] and
          imports_unchanged and code == 0 and bool(rows) and passed == len(rows))
    info = [
        ("timestamp_utc", datetime.now(timezone.utc).isoformat(timespec="seconds")),
        ("platform", platform.platform()),
        ("python", platform.python_version()),
        ("torch", package_version("torch")),
        ("numpy", package_version("numpy")),
        ("pandas", package_version("pandas")),
        ("pytest", package_version("pytest")),
        ("upstream_revision", before["revision"]),
        ("upstream_revision_expected", EXPECTED_REVISION),
        ("upstream_revision_matches", str(before["revision"] == EXPECTED_REVISION)),
        ("upstream_git_root", before["git_root"]),
        ("upstream_preflight_ok", str(before["ok"])),
        ("upstream_tracked_clean_before", str(before["tracked_clean"])),
        ("upstream_added_python_sources_before", json.dumps(before["untracked_package_sources"])),
        ("upstream_imports_verified_before", str(before["imports_match"])),
        ("upstream_imports_before", json.dumps(before["imports"], sort_keys=True)),
        ("upstream_postflight_ok", str(after["ok"]) if after else "not run"),
        ("upstream_revision_after", after["revision"] if after else "not run"),
        ("upstream_tracked_clean_after", str(after["tracked_clean"]) if after else "not run"),
        ("upstream_added_python_sources_after", json.dumps(after["untracked_package_sources"]) if after else "not run"),
        ("upstream_imports_verified_after", str(after["imports_match"]) if after else "not run"),
        ("upstream_imports_after", json.dumps(after["imports"], sort_keys=True) if after else "{}"),
        ("upstream_imports_unchanged", str(imports_unchanged) if after else "not run"),
        ("upstream_provenance_error", provenance_error),
        ("pytest_exit_code", str(code) if code is not None else "not run"),
        ("tests_passed", f"{passed}/{len(rows)}"),
        ("run_status", "PASS" if ok else "FAIL"),
    ]
    write_csv(RESULTS / "python_run_info.csv",
              [{"key": key, "value": value} for key, value in info], ["key", "value"])
    for key, value in info:
        print(f"{key}: {value}")

    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
