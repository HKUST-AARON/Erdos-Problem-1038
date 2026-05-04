#!/usr/bin/env python3
"""Run two-interval slab diagnostics in parallel.

This is a driver around ``verify_two_interval_epsilon_slabs.py``.  It does not
change the certificate logic; it just fans out adjacent epsilon slabs and
kernel/radius choices so remote machines can use multiple cores.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
VERIFIER = ROOT / "verify_two_interval_epsilon_slabs.py"


def adjacent_slabs(json_path: Path) -> list[tuple[float, float]]:
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list) or len(rows) < 2:
        raise SystemExit(f"{json_path}: expected at least two rows")
    epsilons = sorted(float(row["epsilon"]) for row in rows)
    return list(zip(epsilons, epsilons[1:]))


def run_command(command: list[str]) -> tuple[int, str]:
    completed = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    return completed.returncode, completed.stdout


def build_command(args: argparse.Namespace, slab: tuple[float, float], kernel: str, radius: str) -> list[str]:
    eta_counts = args.eta_counts
    command = [
        sys.executable,
        str(VERIFIER),
        str(args.json_path),
        "--slab",
        f"{slab[0]:.17g}:{slab[1]:.17g}",
        "--center",
        "affine-endpoints",
        "--uv-radii",
        radius,
        "--arb-box-dk-subdivisions",
        f"{args.eta_samples},{args.uv_subdivisions}",
        "--dk11-eta-radius-report",
        eta_counts,
        "--dk11-sample-grid",
        str(args.sample_grid),
        "--eta-interval-dk-kernel",
        kernel,
    ]
    return command


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_path", type=Path)
    parser.add_argument("--workers", type=int, default=min(20, os.cpu_count() or 1))
    parser.add_argument("--kernels", default="acb,residue-log")
    parser.add_argument("--uv-radii-list", default="0.01,0.01")
    parser.add_argument("--eta-counts", default="16")
    parser.add_argument("--eta-samples", type=int, default=1)
    parser.add_argument("--uv-subdivisions", type=int, default=2)
    parser.add_argument("--sample-grid", type=int, default=2)
    args = parser.parse_args()

    slabs = adjacent_slabs(args.json_path)
    kernels = [item for item in args.kernels.split(",") if item]
    radii = [item for item in args.uv_radii_list.split(";") if item]
    jobs = [(slab, kernel, radius, build_command(args, slab, kernel, radius)) for slab in slabs for kernel in kernels for radius in radii]

    print(
        f"PARALLEL SLAB DIAGNOSTICS jobs={len(jobs)} workers={args.workers} "
        f"slabs={len(slabs)} kernels={','.join(kernels)} radii={';'.join(radii)}"
    )
    failed = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.workers)) as executor:
        future_map = {executor.submit(run_command, command): (slab, kernel, radius, command) for slab, kernel, radius, command in jobs}
        for future in concurrent.futures.as_completed(future_map):
            slab, kernel, radius, command = future_map[future]
            returncode, output = future.result()
            status = "PASS" if returncode == 0 else "FAIL"
            if returncode != 0:
                failed += 1
            print(
                f"--- job {status} slab={slab[0]:g}:{slab[1]:g} kernel={kernel} "
                f"uv_radii={radius} rc={returncode}"
            )
            print("$ " + " ".join(command))
            print(output.rstrip())
    print(f"PARALLEL SLAB DIAGNOSTICS COMPLETE failed={failed} total={len(jobs)}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
