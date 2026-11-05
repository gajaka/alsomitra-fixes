"""Rebuild/audit Lean and exercise the PyTorch CPU float32 bridge.

Run with a Python environment that already has torch installed.
"""
from collections import Counter
from datetime import datetime, timezone
import argparse
import json
import platform
import subprocess
import sys
import time

import torch

from check_float32 import run_checks
from check_upstream_float32 import run_upstream
from torch_bridge import LeanClient, ROOT, sha, source_hashes
from verify import (ALLOWED_AXIOMS, AXIOMS, BUILD, RESULTS, ensure, execute,
                    require_clean, source_hashes as baseline_hashes)

NAMES = ("decode_none_iff", "admissible_iff", "observe_satisfied_iff", "observe_violated_iff",
         "observe_outside_iff", "physicalMonitor_satisfied_iff", "physicalMonitor_violated_iff",
         "physicalMonitor_outside_iff")


def audit(log):
    rows = AXIOMS.findall(log)
    expected = {"Contribution.Float32." + name for name in NAMES}
    counts = Counter(name for name, _ in rows)
    ensure(set(counts) == expected and all(n == 1 for n in counts.values()), "incomplete/duplicate float32 audit")
    result = {}
    for name, raw in rows:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        ensure(axioms <= ALLOWED_AXIOMS, f"forbidden axioms: {name}: {axioms}")
        result[name] = sorted(axioms)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", help="optional checkout of property-driven-ml at the documented pin")
    args = parser.parse_args()
    BUILD.mkdir(exist_ok=True)
    RESULTS.mkdir(exist_ok=True)
    started = time.monotonic()
    initial = source_hashes()
    path = RESULTS / "float32_verification.json"
    report = dict(status="RUNNING", timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  sources_sha256=initial, torch_version=torch.__version__, python=sys.version,
                  machine=platform.machine(), platform=platform.platform(), torch_config=torch.__config__.show(),
                  scope="Exact contract over observed binary32 bits; CPU eager pointwise inference; no universal network/IEEE arithmetic proof")
    path.write_text(json.dumps(report, indent=2)+"\n")
    try:
        # Rebuild shared modules and preserve the prior rational-core regression evidence.
        subprocess.run([sys.executable,"-B",str(ROOT/"verify.py")], check=True, timeout=300)
        baseline = json.loads((RESULTS/"verification.json").read_text())
        ensure(baseline["status"] == "PASS" and baseline["sources_sha256"] == baseline_hashes(), "stale baseline")
        report["rational_baseline"] = dict(theorem_roots=len(baseline["theorems"]),
                                           assertions=baseline["runtime"]["assertions"],
                                           report_sha256=sha(RESULTS/"verification.json"))
        for module in ("Float32", "Float32Main"):
            for suffix in ("olean", "c"):
                (BUILD / f"{module}.{suffix}").unlink(missing_ok=True)
            require_clean("build_"+module, execute(["lake","env","lean","-R",str(ROOT),
                          "-o",str(BUILD/f"{module}.olean"),"-c",str(BUILD/f"{module}.c"),str(ROOT/f"{module}.lean")]))
            print("Built " + module, flush=True)
        log = require_clean("float32_audit", execute(["lake","env","lean","-R",str(ROOT),str(ROOT/"Float32Audit.lean")]))
        report["theorems"] = audit(log)
        rows = log.splitlines(keepends=True)
        invalid = ("", "".join(rows[:-1]), log+rows[0], log.replace("propext","sorryAx",1))
        for broken in invalid:
            try:
                audit(broken)
            except RuntimeError:
                pass
            else:
                raise RuntimeError("bad axiom audit accepted")
        report["audit_negative_controls"] = len(invalid)
        print(f"Audited {len(report['theorems'])} float32 theorem roots", flush=True)
        transcript = BUILD/"float32_cases.jsonl"
        with LeanClient(verified=False, transcript=transcript) as client:
            report["runtime"] = run_checks(client)
            if args.upstream:
                report["upstream_integration"] = run_upstream(client,args.upstream)
            report["runtime"]["requests"] = client.requests
        report["runtime"]["transcript_sha256"] = sha(transcript)
        report["artifacts_sha256"] = {f".build/{module}.olean":sha(BUILD/f"{module}.olean")
                                      for module in ("Property2","Protocol","Float32","Float32Main")}
        ensure(initial == source_hashes(), "sources changed during verification")
        report["status"] = "PASS"
        print(f"Float32 checks: {report['runtime']['assertions']} assertions, {report['runtime']['requests']} requests", flush=True)
    except Exception as error:
        report["status"] = "FAIL"
        report["error"] = str(error)
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic()-started, 3)
        path.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")


if __name__ == "__main__":
    main()
