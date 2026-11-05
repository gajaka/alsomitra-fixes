"""Build, audit, and execute the first contribution. Requires the parent Lean setup.

Run: python3 contribution/verify.py
No upstream checkout, training, network service, or Python package is required
once the parent project's Lean/Mathlib dependencies have been installed.
"""
from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from check_runtime import run_checks


ROOT = Path(__file__).resolve().parent
LEAN = ROOT.parent / "lean"
BUILD = ROOT / ".build"
RESULTS = ROOT / "results"
ROOTS = (
    "denormalize_normalize", "normalize_denormalize", "compile_correct",
    "ordered_iff_exists", "compile_nonempty_iff", "normalized_order",
    "normalizeBox_correct", "normalized_compile_correct", "interpolate_mem",
    "sample_sound", "sample_none_iff", "encodeUnit_mem", "interpolate_encodeUnit",
    "sample_complete", "output_threshold_correct", "loss_zero_iff",
    "monitor_satisfied_iff", "monitor_violated_iff", "monitor_outside_iff",
)
EXPECTED = {"Contribution.Property2." + name for name in ROOTS}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]\n]*)\]|does not depend on any axioms)")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes():
    paths = ("Property2.lean", "Protocol.lean", "Main.lean", "Audit.lean", "verify.py", "check_runtime.py")
    return {name: digest(ROOT / name) for name in paths}


def environment():
    env = os.environ.copy()
    env["LEAN_PATH"] = str(BUILD) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    return env


def execute(args, *, stdin=None, timeout=240):
    return subprocess.run(args, cwd=LEAN, env=environment(), input=stdin,
                          text=True, capture_output=True, timeout=timeout)


def ensure(condition, message):
    if not condition:
        raise RuntimeError(message)


def require_clean(label, result):
    log = result.stdout + result.stderr
    (RESULTS / (label + ".log")).write_text(log)
    ensure(result.returncode == 0, f"{label} failed (exit {result.returncode}):\n{log}")
    ensure(not re.search(r"\b(?:warning|error):", log), f"{label} diagnostics:\n{log}")
    return log


def check_audit(log):
    reports = AXIOMS.findall(log)
    counts = Counter(name for name, _ in reports)
    ensure(set(counts) == EXPECTED and all(n == 1 for n in counts.values()),
           "Audit must contain every expected theorem exactly once")
    result = {}
    for name, raw in reports:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        ensure(axioms <= ALLOWED_AXIOMS, f"Forbidden axioms in {name}: {axioms}")
        result[name] = sorted(axioms)
    return result


def audit_negative_controls(log):
    """An incomplete or untrusted report must not look like a successful audit."""
    rows = log.splitlines(keepends=True)
    malformed = (
        "", "".join(rows[:-1]), log + rows[0],
        log.replace("propext", "sorryAx", 1),
        log.replace("Contribution.Property2.compile_correct", "Other.wrong_theorem", 1),
    )
    for invalid in malformed:
        try:
            check_audit(invalid)
        except RuntimeError:
            continue
        raise RuntimeError("Audit negative control was incorrectly accepted")
    return len(malformed)


def main():
    BUILD.mkdir(exist_ok=True)
    RESULTS.mkdir(exist_ok=True)
    started = time.monotonic()
    initial = source_hashes()
    report = dict(status="RUNNING", timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  arithmetic="exact rational", sources_sha256=initial,
                  scope="Executable Lean core; parser tested; no PyTorch/float32/network guarantee")
    (RESULTS / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    try:
        version = require_clean("version", execute(["lake", "env", "lean", "--version"]))
        ensure("version 4.35.0," in version, "Expected the existing Lean 4.35.0 toolchain")
        report["lean_version"] = version.strip()
        manifest = json.loads((LEAN / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        ensure(mathlib["rev"] == "56a005855ea17e0b0958f73ec801ae140b0a1679", "Unexpected Mathlib pin")
        report["mathlib_revision"] = mathlib["rev"]
        # Build these exact sources afresh; imported Mathlib may use its normal cache.
        for module in ("Property2", "Protocol", "Main"):
            for suffix in ("olean", "c"):
                (BUILD / f"{module}.{suffix}").unlink(missing_ok=True)
            require_clean("build_" + module, execute([
                "lake", "env", "lean", "-R", str(ROOT),
                "-o", str(BUILD / (module + ".olean")),
                "-c", str(BUILD / (module + ".c")), str(ROOT / (module + ".lean")),
            ]))
            print(f"Built {module}", flush=True)
        audit = require_clean("audit", execute(["lake", "env", "lean", "-R", str(ROOT), str(ROOT / "Audit.lean")]))
        report["theorems"] = check_audit(audit)
        report["audit_negative_controls"] = audit_negative_controls(audit)
        print(f"Audited {len(report['theorems'])} theorem roots", flush=True)

        # Exercise the real compiler: Normalized cannot be passed to normalize.
        negative = BUILD / "DoubleNormalization.lean"
        negative.write_text("import Property2\nopen Contribution.Property2\n"
                            "example (n : Normalizer) (p : Physical) : Normalized :=\n"
                            "  Contribution.Property2.normalize n (Contribution.Property2.normalize n p)\n")
        rejected = execute(["lake", "env", "lean", "-R", str(BUILD), str(negative)])
        log = rejected.stdout + rejected.stderr
        (RESULTS / "expected_type_rejection.log").write_text(log.replace(str(ROOT), "<contribution>"))
        ensure(rejected.returncode != 0 and "type mismatch" in log.lower()
               and "Normalized" in log and "Physical" in log,
               "Expected typed double-normalization rejection was not observed")
        report["typed_double_normalization_rejected"] = True

        request_count = 0
        raw = BUILD / "runtime_cases.jsonl"
        raw.write_text("")
        def invoke(requests):
            nonlocal request_count
            result = execute(["lake", "env", "lean", "--run", str(ROOT / "Main.lean")],
                             stdin="".join(json.dumps(r) + "\n" for r in requests))
            ensure(result.returncode == 0 and not result.stderr,
                   "Executable adapter failed:\n" + result.stdout + result.stderr)
            replies = [json.loads(line) for line in result.stdout.splitlines()]
            ensure(len(replies) == len(requests), "CLI response count mismatch")
            with raw.open("a") as f:
                for request, reply in zip(requests, replies):
                    f.write(json.dumps(dict(request=request, reply=reply), sort_keys=True) + "\n")
            request_count += len(requests)
            return replies
        report["runtime"] = run_checks(invoke)
        report["runtime"]["requests"] = request_count
        report["runtime"]["transcript_sha256"] = digest(raw)
        ensure(initial == source_hashes(), "Contribution sources changed during verification")
        report["status"] = "PASS"
        print(f"Runtime checks: {report['runtime']['assertions']} assertions, {request_count} requests", flush=True)
    except Exception as error:
        report["status"] = "FAIL"
        report["error"] = str(error)
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        (RESULTS / "verification.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
