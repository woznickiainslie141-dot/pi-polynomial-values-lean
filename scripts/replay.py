"""Serially replay the published endpoint proof using its original Windows job guard."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys

from check_release import PROJECT, PUBLIC, ROOT, check_axioms, source, source_order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--plan", action="store_true", help="Check the local graph without starting Lean.")
    modes.add_argument("--build", action="store_true", help="Compile every local import, then run the four-signature audit.")
    modes.add_argument("--audit-only", action="store_true", help="Use an existing matching local build for the final audit.")
    args = parser.parse_args()

    order = source_order()
    if len(order) != 950 or order[-1] != PUBLIC:
        raise ValueError("The source graph differs from the accepted final closure.")
    print(f"Local proof order: {len(order) - 1} prerequisites, then {PUBLIC}.", flush=True)
    if args.plan:
        return 0
    if os.name != "nt":
        parser.error("The original bounded compiler runner requires Windows.")
    if not (PROJECT / ".lake/packages").is_dir():
        parser.error("Provide the nine pinned upstream checkouts and their compiled caches in .lake/packages.")
    if args.audit_only:
        libdir = PROJECT / ".lake/build/lib/lean"
        for name in order[:-1]:
            artifact = libdir / source(name).relative_to(PROJECT).with_suffix(".olean")
            if not artifact.is_file():
                parser.error(f"Missing compiled local import {name}. Prepare a matching cache or use --build.")
        order = [PUBLIC]

    wrapper = ROOT / "research/pi_low_degree_lean_prep_2026-11-19/check_module.py"
    session = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    logs = Path("logs/replay") / session
    (PROJECT / logs).mkdir(parents=True, exist_ok=False)
    for ordinal, name in enumerate(order, start=1):
        target = source(name).relative_to(PROJECT)
        log = logs / f"{ordinal:04}-{name.rsplit('.', 1)[-1]}.log"
        print(f"[{ordinal}/{len(order)}] {name}", flush=True)
        command = [sys.executable, "-B", str(wrapper), str(target), "--timeout", "180", "--log", str(log)]
        if name != PUBLIC:
            command.append("--emit")
        completed = subprocess.run(command, cwd=ROOT)
        if completed.returncode:
            return completed.returncode
        metrics = json.loads((PROJECT / log).with_suffix(".job.json").read_bytes())
        if not (metrics["process_completed"] and metrics["exit_code"] == 0
                and metrics["job_cap_MiB"] == 6144 and 0 < metrics["peak_job_MiB"] <= 6144):
            raise ValueError(f"Unsuccessful bounded compiler record for {name}.")
        if name == PUBLIC:
            check_axioms((PROJECT / log).read_text(encoding="utf-8"))
            print(f"Verified four signatures and four axiom reports. New audit log: {PROJECT / log}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
