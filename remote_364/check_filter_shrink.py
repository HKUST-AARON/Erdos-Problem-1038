#!/usr/bin/env python3
"""Check whether proposed OpenEvolve filters strictly shrink residue sets."""

from __future__ import annotations

import argparse
import importlib.util
import json

from openevolve_evaluator import independence_report, normalize_filters


def load_program(path: str):
    spec = importlib.util.spec_from_file_location("candidate", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load candidate")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("program", help="candidate python file with proposed_filters()")
    args = parser.parse_args()

    module = load_program(args.program)
    filters, valid = normalize_filters(module.proposed_filters())
    report = independence_report(filters)
    print(
        json.dumps(
            {
                "valid_shape": bool(valid),
                "all_strict": report["redundant"] == 0 and not report["invalid_lcm"],
                **report,
            },
            indent=2,
            ensure_ascii=True,
        )
    )


if __name__ == "__main__":
    main()
