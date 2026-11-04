"""Build the Lean library, audit its axioms and write the results to CSV files.

Usage, from this directory (lean/):

    lake exe cache get            # once, to download prebuilt Mathlib
    python run_lean_audit.py

Needs only Python's standard library, `lake` on the PATH and the toolchain in
lean-toolchain. It does not run the Python tests; those have their own script,
../run_python_tests.py.

Writes:
    results/lean_theorems.csv  one row per theorem listed in Audit.lean
    results/lean_run_info.csv  Lean version, build status, totals

The exit code is nonzero if a command fails, build or audit diagnostics contain
a warning/error, a proof placeholder is found, the audit does not report every
expected theorem exactly once, or a theorem uses a nonstandard axiom.
"""
from __future__ import annotations

import csv
from collections import Counter
import platform
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_THEOREMS = (
    "AlsomitraFixes.upstream_defaults_swapped",
    "AlsomitraFixes.defect1_y_interval_empty",
    "AlsomitraFixes.defect2_hi_agrees_iff",
    "AlsomitraFixes.exceptional_anchor_in_domain",
    "AlsomitraFixes.defect2_wrong_at_xMin",
    "AlsomitraFixes.upstream_box_escapes_band",
    "AlsomitraFixes.Coupled.decode_sound",
    "AlsomitraFixes.Coupled.decode_complete",
    "AlsomitraFixes.region1_wellFormed",
    "AlsomitraFixes.region2_wellFormed",
    "AlsomitraFixes.fixed_property1_candidates_in_band",
    "AlsomitraFixes.paper_theta_strictly_inside_upstream",
)
AXIOM_LINE = re.compile(
    r"'(?P<name>[^'\n]+)' (?:depends on axioms: \[(?P<axioms>[^\]\n]*)\]"
    r"|does not depend on any axioms)"
)
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def run(command):
    try:
        return subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    except OSError as error:
        return subprocess.CompletedProcess(command, 127, "", str(error))


def diagnostics(log):
    """Count plain and source-positioned Lean/Lake diagnostics."""
    log = ANSI_ESCAPE.sub("", log)
    prefix = r"(?m)^(?:[^\n]*?:\d+:\d+:\s*)?\s*"
    return (
        len(re.findall(prefix + r"warning:", log)),
        len(re.findall(prefix + r"error:", log)),
    )


def lean_code(source):
    """Mask strings and nested comments before looking for placeholders."""
    chars = list(source)
    index, depth, string, line_comment = 0, 0, False, False
    while index < len(source):
        pair, char = source[index:index + 2], source[index]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                chars[index] = " "
            index += 1
        elif depth:
            if pair == "/-":
                chars[index:index + 2] = "  "
                depth += 1
                index += 2
            elif pair == "-/":
                chars[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if char != "\n":
                    chars[index] = " "
                index += 1
        elif string:
            if char == "\\" and index + 1 < len(source):
                chars[index:index + 2] = "  "
                index += 2
            else:
                if char == '"':
                    string = False
                if char != "\n":
                    chars[index] = " "
                index += 1
        elif pair == "--":
            chars[index:index + 2] = "  "
            line_comment = True
            index += 2
        elif pair == "/-":
            chars[index:index + 2] = "  "
            depth = 1
            index += 2
        elif char == '"':
            chars[index] = " "
            string = True
            index += 1
        else:
            index += 1
    return "".join(chars)


def declared_theorems(path):
    """Read this package's explicit audit commands, including short names."""
    code = lean_code(path.read_text())
    requests = re.findall(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+([A-Za-z0-9_.]+)[ \t]*$", code)
    count = len(re.findall(r"(?m)^[ \t]*#print[ \t]+axioms\b", code))
    if count != len(requests):
        return ()
    return tuple(name if name.startswith("AlsomitraFixes.") else "AlsomitraFixes." + name
                 for name in requests)


def parse_axioms(log):
    rows = []
    for match in AXIOM_LINE.finditer(ANSI_ESCAPE.sub("", log)):
        axioms = [a.strip() for a in (match["axioms"] or "").split(",") if a.strip()]
        rows.append({
            "theorem": match["name"],
            "axioms": " ".join(axioms),
            "only_standard_axioms": str(set(axioms) <= STANDARD_AXIOMS),
        })
    return rows


def write_csv(path, rows, fields):
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)

    version_result = run(["lake", "env", "lean", "--version"])
    version = version_result.stdout.strip() or "unknown"
    version_ok = version_result.returncode == 0 and bool(version_result.stdout.strip())
    if version_result.stderr:
        print(version_result.stderr, file=sys.stderr)
    build = run(["lake", "build"]) if version_ok else None
    build_log = (build.stdout + build.stderr) if build is not None else "Build not run: Lean version command failed."
    build_warnings, build_errors = diagnostics(build_log)
    print(build_log)

    sources = sorted(ROOT.glob("AlsomitraFixes/**/*.lean")) + [ROOT / "AlsomitraFixes.lean"]
    sorry_hits = [str(path.relative_to(ROOT)) for path in sources
                  if re.search(r"\bsorry\b|\badmit\b", lean_code(path.read_text()))]

    requested = declared_theorems(ROOT / "Audit.lean")
    requests_ok = (len(requested) == len(EXPECTED_THEOREMS)
                   and set(requested) == set(EXPECTED_THEOREMS))
    audit, audit_log, rows = None, "", []
    build_ok = build is not None and build.returncode == 0
    if build_ok and build_warnings == 0 and build_errors == 0 and not sorry_hits and requests_ok:
        audit = run(["lake", "env", "lean", "Audit.lean"])
        audit_log = audit.stdout + audit.stderr
        print(audit_log)
        rows = parse_axioms(audit_log)
    audit_warnings, audit_errors = diagnostics(audit_log)
    counts = Counter(row["theorem"] for row in rows)
    missing = sorted(set(EXPECTED_THEOREMS) - set(counts))
    unexpected = sorted(set(counts) - set(EXPECTED_THEOREMS))
    duplicates = sorted(name for name, count in counts.items() if count != 1)
    coverage_ok = bool(EXPECTED_THEOREMS) and not missing and not unexpected and not duplicates
    audit_ok = audit is not None and audit.returncode == 0
    write_csv(RESULTS / "lean_theorems.csv", rows, ["theorem", "axioms", "only_standard_axioms"])

    nonstandard = sum(row["only_standard_axioms"] != "True" for row in rows)
    info = [
        ("timestamp_utc", datetime.now(timezone.utc).isoformat(timespec="seconds")),
        ("platform", platform.platform()),
        ("lean", version),
        ("version_ok", str(version_ok)),
        ("version_exit_code", str(version_result.returncode)),
        ("build_ok", str(build_ok)),
        ("build_exit_code", str(build.returncode) if build is not None else "not run"),
        ("build_warnings", str(build_warnings)),
        ("build_errors", str(build_errors)),
        ("files_with_sorry", " ".join(sorry_hits) or "none"),
        ("audit_requests_match_expected", str(requests_ok)),
        ("audit_ok", str(audit_ok)),
        ("audit_exit_code", str(audit.returncode) if audit is not None else "not run"),
        ("audit_warnings", str(audit_warnings)),
        ("audit_errors", str(audit_errors)),
        ("theorems_expected", str(len(EXPECTED_THEOREMS))),
        ("theorems_audited", str(len(rows))),
        ("audit_coverage_complete", str(coverage_ok)),
        ("missing_theorems", " ".join(missing) or "none"),
        ("unexpected_theorems", " ".join(unexpected) or "none"),
        ("duplicate_theorems", " ".join(duplicates) or "none"),
        ("theorems_with_nonstandard_axioms", str(nonstandard)),
    ]
    write_csv(RESULTS / "lean_run_info.csv",
              [{"key": key, "value": value} for key, value in info], ["key", "value"])
    for key, value in info:
        print(f"{key}: {value}")

    ok = (version_ok and build_ok and build_warnings == 0 and build_errors == 0
          and not sorry_hits and requests_ok and audit_ok and audit_warnings == 0
          and audit_errors == 0 and coverage_ok and nonstandard == 0)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
