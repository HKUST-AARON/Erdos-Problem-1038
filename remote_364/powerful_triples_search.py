#!/usr/bin/env python3
"""Deterministic search for three consecutive powerful numbers.

Every powerful number has the unique form a^2 b^3 with b squarefree.
This script generates that set up to N, sorts it, and scans for runs of
three consecutive values. It is meant as computational evidence, not as a
proof of the Erdős-Mollin-Walsh conjecture.
"""

from __future__ import annotations

import argparse
import json
import math
import resource
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_OUT = SCRIPT_DIR / "powerful_search_result.json"


def integer_cuberoot(n: int) -> int:
    lo, hi = 0, 1
    while hi**3 <= n:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def squarefree_sieve(n: int) -> bytearray:
    squarefree = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        squarefree[0] = 0
    for p in range(2, math.isqrt(n) + 1):
        pp = p * p
        squarefree[pp : n + 1 : pp] = b"\x00" * (((n - pp) // pp) + 1)
    return squarefree


def rss_mb() -> float:
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0


def search(limit: int, progress_every: int, out: Path) -> dict:
    started = time.time()
    bmax = integer_cuberoot(limit)
    squarefree = squarefree_sieve(bmax)
    values: list[int] = []
    generated = 0

    for b in range(1, bmax + 1):
        if not squarefree[b]:
            continue
        b3 = b * b * b
        amax = math.isqrt(limit // b3)
        for a in range(1, amax + 1):
            values.append(a * a * b3)
        generated += amax
        if progress_every and b % progress_every == 0:
            print(
                json.dumps(
                    {
                        "phase": "generate",
                        "b": b,
                        "bmax": bmax,
                        "values": len(values),
                        "rss_mb": round(rss_mb(), 1),
                        "seconds": round(time.time() - started, 1),
                    },
                    ensure_ascii=True,
                ),
                flush=True,
            )

    values.sort()
    triples: list[int] = []
    adjacent_pairs = 0
    prev2 = None
    prev1 = None
    unique_count = 0

    for v in values:
        if prev1 == v:
            continue
        unique_count += 1
        if prev1 is not None and v == prev1 + 1:
            adjacent_pairs += 1
        if prev2 is not None and prev1 is not None and prev1 == prev2 + 1 and v == prev1 + 1:
            triples.append(prev2)
            print(json.dumps({"phase": "hit", "x": prev2}, ensure_ascii=True), flush=True)
        prev2, prev1 = prev1, v

    result = {
        "limit": limit,
        "bmax": bmax,
        "generated": generated,
        "unique_count": unique_count,
        "adjacent_pairs": adjacent_pairs,
        "triple_starts": triples,
        "triple_count": len(triples),
        "seconds": round(time.time() - started, 3),
        "max_rss_mb": round(rss_mb(), 1),
    }
    out.write_text(json.dumps(result, indent=2, ensure_ascii=True) + "\n")
    print(json.dumps({"phase": "done", **result}, ensure_ascii=True), flush=True)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=10**14)
    parser.add_argument("--progress-every", type=int, default=1000)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    search(args.limit, args.progress_every, args.out)


if __name__ == "__main__":
    main()
