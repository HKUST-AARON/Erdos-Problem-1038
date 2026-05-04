#!/usr/bin/env python3
"""Compatibility verifier for the 560-block candidate.

This wrapper uses the required-domain checker, consistent with the normalized
support assumption used in the finite-atom route.
"""

import argparse
import json
from pathlib import Path

from verify_piecewise_tail_correct_domain import verify_required_domain, scan_overcheck_gap


def _load_candidate(path: Path):
    with path.open("r") as f:
        return json.load(f)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--gap-scan",
        action="store_true",
        help="also scan the irrelevant middle gap [A-1, C]",
    )
    args = parser.parse_args()

    cert_path = (
        Path(__file__).resolve().parent.parent
        / "data"
        / "piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json"
    )
    cert = _load_candidate(cert_path)

    worst, bad = verify_required_domain(cert)
    print("Certificate:", cert.get("name", str(cert_path)))
    print("M =", cert["M"], "K =", cert["K"])
    print("Required-domain worst margin:", "{:.12g}".format(worst[0]))
    print("Required-domain worst block:", worst[1], "y =", "{:.15g}".format(worst[2]))
    print("Bad required-domain blocks:", len(bad))

    if args.gap_scan:
        gap = scan_overcheck_gap(cert)
        print()
        print("Irrelevant middle-gap overcheck worst:", "{:.12g}".format(gap[0]))
        print("Irrelevant middle-gap block:", gap[1], "y =", "{:.15g}".format(gap[2]))


if __name__ == "__main__":
    main()
